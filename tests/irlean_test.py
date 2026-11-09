#!/usr/bin/env python3
"""Checks tools/irlean, the shared Python library, without LLVM or Lean, in a few seconds: that a command's
limits are kept and never pass for a success, that everything it started is killed, including processes in
sessions of their own, that its cost is measured in MiB on macOS and Linux, that the heavy-job lock is
exclusive and in the platform's cache directory, that hashes are SHA-256 and a tree's read back one way, that
Lean's limits and messages are read as tools/verify.py and tests/proofs.sh read them, that every schema in the
repo is named once, and that the pins are read from the repo's pin files. docs/python.md.

usage: tests/irlean_test.py
"""

import hashlib
import json
import os
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from typing import ClassVar
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from irlean import hashing, lean, pins, proc, schemas  # noqa: E402

PY = sys.executable


def alive(pid: int) -> bool:
    """Running, not a zombie waiting to be reaped."""
    r = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True, check=False)
    return r.returncode == 0 and bool(r.stdout.strip()) and not r.stdout.strip().startswith("Z")


def gone(pid: int, seconds: float = 5) -> bool:
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline and alive(pid):
        time.sleep(0.05)
    return not alive(pid)


# A root that starts a child in a session of its own, writes the child's pid to argv[1], and waits for it, as
# every step tools/binding.py runs does.
SESSION_CHILD = (
    "import subprocess, sys; p = subprocess.Popen([sys.executable, '-c', {child!r}], "
    "start_new_session=True); open(sys.argv[1], 'w').write(str(p.pid)); p.wait()"
)


class Run(unittest.TestCase):
    def test_output_is_captured_as_bytes(self) -> None:
        r = proc.run([PY, "-c", "import sys; sys.stdout.write('out'); sys.stderr.write('err'); sys.exit(3)"])
        self.assertEqual((r.exit, r.stdout, r.stderr, r.limit), (3, b"out", b"err", None))
        self.assertEqual((r.out, r.err, r.output), ("out", "err", "outerr"))
        self.assertFalse(r.ok)

    def test_stderr_can_follow_stdout(self) -> None:
        code = "import sys; print('a', flush=True); print('b', file=sys.stderr, flush=True); print('c')"
        r = proc.run([PY, "-c", code], stderr=proc.STDOUT)
        self.assertEqual((r.stdout, r.stderr), (b"a\nb\nc\n", b""))

    def test_stdin_env_and_cwd(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            code = "import os, sys; print(sys.stdin.read(), os.environ['X'], os.getcwd())"
            r = proc.run([PY, "-c", code], stdin="in", env={**os.environ, "X": "x"}, cwd=d)
            self.assertEqual(r.out.split(), ["in", "x", str(Path(d).resolve())])
            self.assertTrue(r.ok)

    def test_no_stdin_is_empty(self) -> None:
        r = proc.run([PY, "-c", "import sys; print(repr(sys.stdin.read()))"])
        self.assertEqual(r.out.strip(), "''")

    def test_stdin_can_be_this_process_own(self) -> None:
        # As tools/measure.py runs a command: reading what was piped to it.
        inner = "import sys; print(sys.stdin.read())"
        code = (
            "import sys; sys.path.insert(0, sys.argv[1]); from irlean import proc; "
            f"print(proc.run([sys.executable, '-c', {inner!r}], stdin=proc.INHERIT).out)"
        )
        r = proc.run([PY, "-c", code, str(ROOT / "tools")], stdin="payload")
        self.assertEqual(r.out.strip(), "payload")
        # Text that spells it is still text.
        self.assertEqual(proc.run([PY, "-c", inner], stdin="inherit").out.strip(), "inherit")

    def test_output_to_a_file(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            log = Path(d) / "log"
            r = proc.run([PY, "-c", "print('x')"], stdout=log)
            self.assertEqual((log.read_text(), r.stdout), ("x\n", b""))

    def test_a_missing_program_raises(self) -> None:
        with self.assertRaises(FileNotFoundError):
            proc.run(["/nonexistent/program"])

    def test_a_signal_is_not_an_exit_code(self) -> None:
        r = proc.run([PY, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGKILL)"])
        self.assertEqual((r.exit, r.signal, r.limit), (-9, 9, None))
        self.assertFalse(r.ok)

    def test_a_timeout_is_not_a_success(self) -> None:
        r = proc.run([PY, "-c", "import time; time.sleep(30)"], timeout=0.5)
        self.assertEqual(r.limit, "time_limit")
        self.assertFalse(r.ok)
        self.assertLess(r.seconds, 10)

    def test_a_cap_stops_the_whole_tree(self) -> None:
        argv = [PY, "-c", "import time; x = bytearray(200 << 20); time.sleep(30)"]
        r = proc.run(argv, timeout=60, cap_mb=64, interval=0.05)
        self.assertEqual(r.limit, "resource_limit")
        self.assertFalse(r.ok)
        self.assertLess(r.seconds, 30)

    def test_a_limit_kills_descendants_in_sessions_of_their_own(self) -> None:
        child = "import time; x = bytearray({mb} << 20); time.sleep(60)"
        for mb, cap, timeout, outcome in ((200, 64, 60, "resource_limit"), (1, None, 1, "time_limit")):
            with tempfile.TemporaryDirectory() as d:
                pidfile = Path(d) / "pid"
                argv = [PY, "-c", SESSION_CHILD.format(child=child.format(mb=mb)), str(pidfile)]
                r = proc.run(argv, timeout=timeout, cap_mb=cap, interval=0.05)
                self.assertEqual(r.limit, outcome)
                pid = int(pidfile.read_text())
                self.assertTrue(gone(pid), f"{outcome} left pid {pid} running")

    def test_what_the_command_leaves_in_its_group_is_killed(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            pidfile = Path(d) / "pid"
            code = (
                "import subprocess, sys; p = subprocess.Popen([sys.executable, '-c', 'import time; "
                "time.sleep(60)']); open(sys.argv[1], 'w').write(str(p.pid))"
            )
            r = proc.run([PY, "-c", code, str(pidfile)], timeout=60)
            self.assertTrue(r.ok)
            self.assertLess(r.seconds, 30, "it waited for what the command left running")
            self.assertTrue(gone(int(pidfile.read_text())))

    def test_output_held_open_by_a_descendant_does_not_hold_it_up(self) -> None:
        # The descendant keeps the command's stdout open, in a session of its own, where killing the group
        # doesn't reach. With pipes, reading the output would wait for it.
        with tempfile.TemporaryDirectory() as d:
            pidfile = Path(d) / "pid"
            argv = [
                PY,
                "-c",
                SESSION_CHILD.format(child="import time; time.sleep(5)").replace("p.wait()", "0"),
            ]
            r = proc.run([*argv, str(pidfile)], timeout=60)
            self.assertLess(r.seconds, 4)
            os.kill(int(pidfile.read_text()), signal.SIGKILL)

    def test_a_child_peak_is_counted(self) -> None:
        child = "import subprocess, sys; subprocess.run([sys.executable, '-c', 'x = bytearray(100 << 20)'])"
        r = proc.run([PY, "-c", child], timeout=60)
        self.assertTrue(r.ok)
        self.assertGreater(r.peak_process_mb, 95)

    @unittest.skipUnless(sys.platform.startswith("linux"), "RLIMIT_AS is only enforced on Linux")
    def test_an_address_limit(self) -> None:
        r = proc.run([PY, "-c", "x = bytearray(500 << 20)"], address_mb=200)
        self.assertNotEqual(r.exit, 0)
        self.assertIn("MemoryError", r.err)
        self.assertTrue(proc.run([PY, "-c", "x = bytearray(10 << 20)"], address_mb=200).ok)

    @unittest.skipUnless(proc.scopes_work(), "no systemd user scopes here")
    def test_a_scope_caps_memory_and_holds_every_descendant(self) -> None:
        scope = proc.Scope("ir-lean-irlean-test", 100)
        hog = "x = bytearray(400 << 20); x[::4096] = b'1' * len(x[::4096])"
        r = proc.run([PY, "-c", hog], scope=scope)
        self.assertEqual((r.limit, r.ok), ("resource_limit", False))
        # A parent that ignores the child the cap killed, and SIGTERM, still doesn't succeed: the whole scope
        # goes at once.
        parent = (
            "import signal, subprocess, sys; signal.signal(signal.SIGTERM, signal.SIG_IGN); "
            f"subprocess.run([sys.executable, '-c', {hog!r}]); print('carried on')"
        )
        r = proc.run([PY, "-c", parent], scope=scope)
        self.assertEqual((r.limit, r.ok), ("resource_limit", False), r.out)
        self.assertNotIn("carried on", r.out)
        with tempfile.TemporaryDirectory() as d:
            pidfile = Path(d) / "pid"
            argv = [
                PY,
                "-c",
                SESSION_CHILD.format(child="import time; time.sleep(60)").replace("p.wait()", "0"),
            ]
            r = proc.run([*argv, str(pidfile)], scope=scope, timeout=60)
            self.assertTrue(r.ok)
            self.assertTrue(gone(int(pidfile.read_text())), "the scope left a descendant running")

    def test_spawn_and_stop(self) -> None:
        p = proc.spawn(
            [
                PY,
                "-c",
                "import sys, time; print(sys.stdin.readline().strip()[::-1], flush=True); time.sleep(60)",
            ],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
        )
        assert p.stdin is not None and p.stdout is not None
        p.stdin.write("abc\n")
        p.stdin.flush()
        self.assertEqual(p.stdout.readline().strip(), "cba")
        proc.stop(p, grace=0.1)
        p.stdout.close()
        self.assertIsNotNone(p.returncode)
        self.assertNotIn(p.pid, proc._LIVE)
        self.assertTrue(p.stdin.closed)

    def test_rss(self) -> None:
        p = proc.spawn(
            [PY, "-c", "import time; x = bytearray(80 << 20); x[::4096] = b'1' * 20480; time.sleep(60)"]
        )
        deadline = time.monotonic() + 10
        while (proc.rss_mb(p.pid) or 0) < 70 and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertGreater(proc.rss_mb(p.pid) or 0, 70)
        proc.stop(p)
        self.assertIsNone(proc.rss_mb(p.pid))

    def test_kill_live_stops_every_running_command(self) -> None:
        p = proc.spawn([PY, "-c", "import time; time.sleep(60)"])
        proc.kill_live()
        self.assertEqual(p.wait(timeout=5), -signal.SIGKILL)
        proc.stop(p)


class Measure(unittest.TestCase):
    def test_maxrss_is_bytes_on_macos_and_kib_on_linux(self) -> None:
        with mock.patch.object(proc.sys, "platform", "darwin"):
            self.assertEqual(proc.maxrss_mib(300 << 20), 300)
        with mock.patch.object(proc.sys, "platform", "linux"):
            self.assertEqual(proc.maxrss_mib(300 << 10), 300)

    def test_a_record_names_its_outcome(self) -> None:
        for code, timeout, cap, outcome in (
            ("pass", 60, None, "ok"),
            ("raise SystemExit(4)", 60, None, "failed"),
            ("import time; time.sleep(30)", 0.5, None, "time_limit"),
            ("import time; x = bytearray(200 << 20); time.sleep(30)", 60, 64, "resource_limit"),
        ):
            r = proc.measure([PY, "-c", code], label="t", timeout=timeout, cap_mb=cap, interval=0.05)
            self.assertEqual(r["outcome"], outcome, code)
            self.assertEqual(r["schema"], schemas.MEASUREMENT)
            self.assertGreaterEqual(r["samples"], 1)

    def test_the_record_keeps_its_fields(self) -> None:
        r = proc.measure([PY, "-c", "pass"], label="fields", timeout=60, cap_mb=None)
        self.assertEqual(
            list(r),
            "schema label command cwd started host outcome exit wall_s user_s sys_s peak_process_mb "
            "peak_tree_mb peak_tree_processes peak_by_command_mb samples sample_interval_s limits "
            "memory_before memory_after".split(),
        )

    def test_the_command_line_tool_records_one_line(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "m.jsonl"
            argv = [PY, str(ROOT / "tools" / "measure.py"), "run", "--label", "cli", "--out", str(out)]
            r = subprocess.run([*argv, "--", PY, "-c", "pass"], capture_output=True, text=True, check=False)
            self.assertEqual(r.returncode, 0, r.stderr)
            record = json.loads(out.read_text())
            self.assertEqual((record["outcome"], record["workers"], record["heavy_lock"]), ("ok", 1, None))
            r = subprocess.run(
                [*argv, "--", PY, "-c", "raise SystemExit(5)"], capture_output=True, check=False
            )
            self.assertEqual(r.returncode, 5)
            # It reads what's piped to measure.py, as it would alone.
            read = [PY, "-c", "import sys; assert sys.stdin.read() == 'payload'"]
            r = subprocess.run([*argv, "--", *read], input=b"payload", capture_output=True, check=False)
            self.assertEqual(r.returncode, 0, r.stderr)

    def test_the_lock_is_in_the_platform_cache_directory(self) -> None:
        home = Path.home()
        cases = (
            ("darwin", {}, home / "Library" / "Caches" / "ir-lean" / "heavy-job.lock"),
            ("linux", {}, home / ".cache" / "ir-lean" / "heavy-job.lock"),
            ("linux", {"XDG_CACHE_HOME": "/xdg"}, Path("/xdg/ir-lean/heavy-job.lock")),
            ("linux", {"XDG_CACHE_HOME": "relative"}, home / ".cache" / "ir-lean" / "heavy-job.lock"),
            ("darwin", {"IR_LEAN_HEAVY_LOCK": "/x.lock"}, Path("/x.lock")),
        )
        for platform, env, want in cases:
            clean = {k: v for k, v in os.environ.items() if k not in ("XDG_CACHE_HOME", "IR_LEAN_HEAVY_LOCK")}
            with (
                mock.patch.object(proc.sys, "platform", platform),
                mock.patch.dict(os.environ, clean | env, clear=True),
            ):
                self.assertEqual(proc.lock_path(), want, (platform, env))

    def test_the_lock_is_exclusive(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            path = str(Path(d) / "heavy-job.lock")
            with mock.patch.dict(os.environ, {"IR_LEAN_HEAVY_LOCK": path}):
                with (
                    proc.heavy_lock("first", 0),
                    self.assertRaisesRegex(TimeoutError, "first"),
                    proc.heavy_lock("second", 0),
                ):
                    pass
                with proc.heavy_lock("after", 0):
                    pass

    def test_memory_is_read(self) -> None:
        m = proc.memory()
        self.assertGreater(m["total_mb"], 0)
        self.assertIsNone(proc.too_busy(0))
        self.assertIsNotNone(proc.too_busy(1 << 40))


class Hashing(unittest.TestCase):
    def test_sha256(self) -> None:
        self.assertEqual(hashing.sha256(b"x"), hashlib.sha256(b"x").hexdigest())
        self.assertEqual(hashing.sha256_text("é"), hashlib.sha256("é".encode()).hexdigest())
        self.assertEqual(hashing.sha256_parts("a", b"b"), hashlib.sha256(b"a\0b\0").hexdigest())
        h = hashing.new(b"a")
        h.update(b"b")
        self.assertEqual(h.hexdigest(), hashlib.sha256(b"ab").hexdigest())
        self.assertEqual(hashing.canonical({"b": 1, "a": "é"}), '{"a":"é","b":1}'.encode())

    def test_a_file_is_hashed_in_pieces(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "big"
            data = os.urandom(3 << 20)
            f.write_bytes(data)
            self.assertEqual(hashing.sha256_file(f), hashlib.sha256(data).hexdigest())
            self.assertEqual(hashing.sha256_files([f]), {f: hashlib.sha256(data).hexdigest()})

    def tree(self, d: Path, files: dict[str, bytes], dirs: tuple[str, ...] = ()) -> str:
        root = d / "root"
        root.mkdir()
        for name in dirs:
            (root / name).mkdir(parents=True)
        for name, data in files.items():
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_bytes(data)
        return hashing.tree_hash(d, root)

    def test_no_two_trees_hash_the_same(self) -> None:
        trees = [
            ({"a": b"x"}, ()),
            ({"a": b"y"}, ()),
            ({"b": b"x"}, ()),
            ({"a": b""}, ()),
            ({}, ("a",)),
            ({"a/b": b"x"}, ()),
            ({"a": b"x", "b": b""}, ()),
            ({"ab": b"x"}, ()),
        ]
        seen = set()
        for files, dirs in trees:
            with tempfile.TemporaryDirectory() as d:
                seen.add(self.tree(Path(d), files, dirs))
        self.assertEqual(len(seen), len(trees))

    def test_a_tree_hash_is_its_bytes_and_paths_only(self) -> None:
        hashes = set()
        for _ in range(2):
            with tempfile.TemporaryDirectory() as d:
                hashes.add(self.tree(Path(d), {"a": b"x", "c/d": b"y"}))
        self.assertEqual(len(hashes), 1)

    def test_links_must_stay_inside_what_is_hashed(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "root"
            root.mkdir()
            (root / "a").write_bytes(b"x")
            (root / "sibling").symlink_to("a")
            hashing.tree_hash(Path(d), root)
            outside = Path(d) / "outside"
            outside.write_bytes(b"secret")
            for target in (str(outside), "../outside", ".", "missing"):
                (root / "bad").symlink_to(target)
                with self.assertRaises(hashing.UntrustedLink, msg=target):
                    hashing.tree_hash(Path(d), root)
                (root / "bad").unlink()

    def test_a_root_that_is_a_link_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "real").mkdir()
            (Path(d) / "root").symlink_to("real")
            with self.assertRaises(hashing.UntrustedLink):
                hashing.tree_hash(Path(d), Path(d) / "root")

    def test_a_stamp_sees_every_write(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "a").write_bytes(b"x")
            before = hashing.stamp(root)
            self.assertEqual(hashing.stamp(root), before)
            (root / "a").write_bytes(b"y")
            self.assertNotEqual(hashing.stamp(root), before)
            snap = hashing.snapshot(root)
            self.assertEqual(snap[str(root / "a")], hashlib.sha256(b"y").hexdigest())
            (root / "l").symlink_to("a")
            self.assertEqual(hashing.snapshot(root)[str(root / "l")], "link a")
            self.assertTrue(stat.S_ISLNK(hashing.stamp(root)[str(root / "l")][0]))


class Lean(unittest.TestCase):
    # What Lean prints at each limit, as tools/verify.py's tests and tests/proofs.sh have seen it.
    SAID: ClassVar[dict[str, str]] = {
        "memory_limit": "error: (kernel) excessive memory consumption detected",
        "heartbeat_limit": "error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)",
        "recursion_limit": "error: maximum recursion depth has been reached",
        "stack_limit": "Stack overflow detected. Aborting.",
        "solver_limit": "error: The SAT solver timed out while solving the problem.",
        "step_limit": "error: simp failed, maximum number of steps exceeded: 100000",
    }

    def test_each_limit_is_read(self) -> None:
        for reason, text in self.SAID.items():
            self.assertEqual(lean.limit_of(text), reason)
            self.assertTrue(lean.is_limit(text), text)
        for text in ("error: type mismatch", "unsolved goals", "error: unknown identifier 'heartbeat'"):
            self.assertIsNone(lean.limit_of(text))
            self.assertFalse(lean.is_limit(text))

    def test_messages(self) -> None:
        out = (
            "A.lean:3:4: error: type mismatch\n  more\n\n"
            "A.lean:5:0: warning(linter): unused\nB.lean:1:0: info: x\n"
        )
        found = lean.messages(out)
        self.assertEqual(
            [(m.severity, m.line, m.column) for m in found],
            [("error", 3, 4), ("warning", 5, 0), ("info", 1, 0)],
        )
        self.assertEqual(found[0].text, "type mismatch\n  more")
        self.assertEqual(lean.errors(out), ["A.lean:3:4: error: type mismatch"])

    def test_argv_and_env(self) -> None:
        self.assertEqual(lean.argv(4000, "a.lean"), ["lean", "-M", "4000", "-s", "65536", "a.lean"])
        self.assertEqual(
            lean.argv(3000, "a.lean", lean="/l", threads=1),
            ["/l", "-j1", "-M", "3000", "-s", "65536", "a.lean"],
        )
        self.assertEqual(lean.argv(1, stack_kb=None), ["lean", "-M", "1"])
        self.assertEqual(lean.checker("A", "B"), ["leanchecker", "A", "B"])
        env = lean.env("/w", base={"PATH": "/bin"}, pin=True, X="1")
        self.assertEqual(env["LEAN_PATH"], f"/w{os.pathsep}{lean.LIBRARY}")
        self.assertEqual((env["PATH"], env["X"], env["ELAN_TOOLCHAIN"]), ("/bin", "1", lean.toolchain()))
        audit = lean.audit_env("M", "G", "T Ns.f", base={"A": "1"})
        self.assertEqual(
            audit,
            {
                "A": "1",
                "IRLEAN_CHECK_MODULE": "M",
                "IRLEAN_CHECK_GENERATED": "G",
                "IRLEAN_CHECK_THEOREMS": "T Ns.f",
            },
        )
        self.assertEqual(lean.audit_argv(2000)[-1], str(ROOT / "tests" / "check_axioms.lean"))

    def test_the_shell_tests_count_no_limit_this_does_not(self) -> None:
        # The shell tests keep their own copy. tests/proofs.sh's has to be this one, and none may have a limit
        # this doesn't, or a step one stops at could count here as failing on its own.
        alternatives = set(lean.LIMIT.pattern.split("|"))
        for script in ("proofs.sh", "contracts.sh", "refine.sh", "generic_rewrites.sh", "undef_freeze.sh"):
            text = (ROOT / "tests" / script).read_text()
            pattern = "".join(re.findall(r"^limit\+?='([^']*)'", text, re.M))
            self.assertTrue(pattern, script)
            self.assertLessEqual(set(pattern.split("|")), alternatives, script)
            if script == "proofs.sh":
                self.assertEqual(pattern, lean.LIMIT.pattern)


class Schemas(unittest.TestCase):
    def test_names(self) -> None:
        self.assertGreaterEqual(len(schemas.ALL), 22)
        for name in schemas.ALL:
            self.assertRegex(name, schemas.NAME)

    def test_every_schema_in_the_repo_is_named_here(self) -> None:
        literal = re.compile(r"""["'](ir-lean\.[a-z0-9][a-z0-9_.-]*/\d+)["']""")
        tracked = subprocess.run(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard", "*.py"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.split()
        unknown = {}
        for name in tracked:
            path = ROOT / name
            if not path.exists() or name.endswith("_test.py") or name == "tools/irlean/schemas.py":
                continue
            for found in literal.findall(path.read_text()):
                # A test writes a version that isn't one, to check it's refused.
                if found not in schemas.ALL and not name.startswith("tests/"):
                    unknown[found] = name
        self.assertEqual(unknown, {})

    def test_reading_checks_the_schema(self) -> None:
        good = {"schema": schemas.VERIFY, "status": "proved"}
        self.assertEqual(schemas.check(good, schemas.VERIFY), good)
        for bad in ({"schema": "ir-lean.verify/2"}, {}, [], "x", {"schema": schemas.BINDING_VERDICT}):
            with self.assertRaises(schemas.SchemaError):
                schemas.check(bad, schemas.VERIFY)
        with self.assertRaises(schemas.SchemaError):
            schemas.check(good, "ir-lean.made-up/1")
        with self.assertRaises(schemas.SchemaError):
            schemas.loads("{", schemas.VERIFY)
        self.assertEqual(schemas.loads(json.dumps(good), schemas.VERIFY), good)

    def test_writing_keeps_the_writers_form_and_replaces_whole(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "sub" / "r.json"
            record = {"schema": schemas.VERIFY, "é": 1}
            schemas.write(path, record, schemas.VERIFY, indent=2, ensure_ascii=False)
            self.assertEqual(path.read_text(), json.dumps(record, indent=2, ensure_ascii=False) + "\n")
            self.assertEqual(schemas.read(path, schemas.VERIFY), record)
            self.assertEqual(stat.S_IMODE(path.stat().st_mode), 0o666 & ~_umask())
            with self.assertRaises(schemas.SchemaError):
                schemas.write(path, {"schema": "x"}, schemas.VERIFY)
            self.assertEqual(schemas.read(path, schemas.VERIFY), record)
            self.assertEqual(sorted(p.name for p in path.parent.iterdir()), ["r.json"])


def _umask() -> int:
    r = subprocess.run(["sh", "-c", "umask"], capture_output=True, text=True, check=True)
    return int(r.stdout.strip(), 8)


class Pins(unittest.TestCase):
    def test_the_pins_are_read_from_their_files(self) -> None:
        llvm = pins.llvm()
        self.assertEqual(set(llvm), {"repository", "tag", "commit", "nix_hash"})
        self.assertRegex(llvm["tag"], r"^llvmorg-\d+\.\d+\.\d+$")
        self.assertRegex(llvm["commit"], r"^[0-9a-f]{40}$")
        self.assertEqual(pins.llvm_version(), llvm["tag"].removeprefix("llvmorg-"))
        self.assertEqual(pins.lean(), (ROOT / "lean-toolchain").read_text().strip())
        alive2 = pins.alive2()
        self.assertRegex(alive2["rev"], r"^[0-9a-f]{40}$")
        self.assertTrue(alive2["nix_hash"].startswith("sha256-"))

    def test_a_tool_is_named_by_its_hash(self) -> None:
        t = pins.tool("sh")
        assert t is not None
        self.assertEqual(t.path, Path(t.path).resolve())
        self.assertEqual(t.sha256, hashlib.sha256(t.path.read_bytes()).hexdigest())
        self.assertIsNone(pins.tool("no-such-program-anywhere"))
        fake = pins.Tool("opt", Path("/opt"), "0" * 64, f"LLVM version {pins.llvm_version()}\n")
        self.assertTrue(fake.matches_llvm_pin())
        self.assertFalse(pins.Tool("opt", Path("/opt"), "0" * 64, "LLVM version 1.0").matches_llvm_pin())


if __name__ == "__main__":
    unittest.main()
