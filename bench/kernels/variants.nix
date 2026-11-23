# Pinned libsodium builds and controls for the kernel corpus. See docs/kernels.md.
# `repo` is the flake's own source, so the manifest, the builder and a workload's driver are one snapshot's.
{
  pkgs,
  repo,
  attempt ? "default",
}:
let
  inherit (pkgs) lib;
  manifest = builtins.fromTOML (builtins.readFile "${repo}/bench/kernels/manifest.toml");
  need =
    what: name: set:
    set.${name} or (throw "bench/kernels/manifest.toml: ${what} has no `${name}`");
  p = need "the manifest" "libsodium" (need "the manifest" "project" manifest);
  entry = need "libsodium";
  m = builtins.match "https://github.com/([^/]+)/([^/]+)" (entry "repository" p);
  src =
    (builtins.fetchTree {
      type = "github";
      owner = builtins.elemAt m 0;
      repo = builtins.elemAt m 1;
      rev = entry "rev" p;
      narHash = entry "nix_hash" p;
    }).outPath;
  # The dev shell's compiler: nix/shell.nix takes its stdenv from llvmPackages_latest too.
  llvm = pkgs.llvmPackages_latest;
  inherit (llvm) stdenv;
  matchesPin =
    tool:
    "llvmorg-${tool.version}" == manifest.corpus.llvm_tag
    && tool.monorepoSrc.outputHash == manifest.corpus.llvm_nix_hash;
  checkHeader = pkgs.runCommand "libsodium-check-header" { nativeBuildInputs = [ pkgs.patch ]; } ''
    cp ${src}/test/default/cmptest.h cmptest.h
    patch --fuzz=0 cmptest.h < ${./libsodium/cmptest-observation.patch}
    cp cmptest.h "$out"
  '';
  out = placeholder "out";

  # A word of one of the manifest's commands, with its placeholders filled in. {build} is the derivation's own
  # output: the build runs in place there. One this doesn't know is an error, not a word passed on.
  word =
    w:
    let
      filled = builtins.replaceStrings [ "{src}" "{build}" "{repo}" ] [ src out "${repo}" ] w;
    in
    if builtins.match ".*\\{[A-Za-z][A-Za-z0-9:_.-]*}.*" filled != null then
      throw "bench/kernels/manifest.toml: libsodium's `${w}` has a placeholder a build doesn't fill in"
    else
      filled;
  command = map word;

  # The compiler the build is given. For a compile whose object the table names, it makes the object from the
  # table's IR with llc, and for any other it runs clang with the words it was given. For a compile of one of the
  # manifest's units it writes down which source gave which object, and runs clang again with the same words but
  # -c and -o, to IR under $KERNELS_OUT/ir. Each is written once: a second compile of one object fails.
  cc = pkgs.writeShellScript "cc-for-kernels" ''
    unit= object= compile= previous=
    for a in "$@"; do
      [ "$previous" = -o ] && object=$a
      [ "$a" = -c ] && compile=1
      while read -r u; do [ "$a" = "$u" ] && unit=$a; done < "$KERNELS_PLAN/units"
      previous=$a
    done
    if [ -n "''${KERNELS_CHECK_MARKER:-}" ]; then
      for a in "$@"; do
        if [ "$a" = "${src}/test/default/pwhash_argon2id.c" ]; then
          set -- -D'TEST_NAME="pwhash_argon2id"' -I"${src}/test/default" -include ${checkHeader} "$@"
          break
        fi
      done
    fi
    key=
    if [ -n "$compile" ] && [ -n "$object" ]; then
      key=$PWD/$object
      key=''${key#"$KERNELS_OUT/"}
    fi
    # A file for each object, written once: with noclobber, a second write fails.
    once() {
      (set -C && printf '%s\n%s\n' "$key" "$2" > "$KERNELS_PLAN/$1/$(printf %s "$key" | sha256sum | cut -c1-64)")
    }
    if [ -n "$key" ] && [ -L "$KERNELS_PLAN/replace/$key" ]; then
      ir=$(readlink -e "$KERNELS_PLAN/replace/$key") && [ -f "$ir" ] || exit 1
      once replacing "$ir" || exit 1
      llc -O3 -relocation-model=pic -filetype=obj "$ir" -o "$object" || exit $?
      [ -s "$object" ] && once replaced "$ir" || exit 1
    else
      clang "$@" || exit $?
    fi
    [ -n "$key" ] && [ -n "$unit" ] || exit 0
    once compiled "$unit" || exit 1
    words=() skip=
    for a in "$@"; do
      if [ -n "$skip" ]; then skip=; continue; fi
      case $a in -c) continue ;; -o) skip=1; continue ;; esac
      words+=("$a")
    done
    mkdir -p "$(dirname "$KERNELS_OUT/ir/$key")"
    exec clang "''${words[@]}" -S -emit-llvm -o "$KERNELS_OUT/ir/$key.ll"
  '';

  # A workload's `run`, resolved: one command, whose leading `env` and NAME=VALUE words are its whole environment,
  # and whose program is a path under the build.
  launch =
    w:
    let
      commands = need "workload ${w.name}" "run" w;
      words =
        if builtins.length commands == 1 then
          command (builtins.head commands)
        else
          throw "bench/kernels/manifest.toml: workload ${w.name}'s `run` isn't one command";
      rest = if builtins.head words == "env" then builtins.tail words else words;
      isSet = a: builtins.match "[A-Za-z_][A-Za-z0-9_]*=.*" a != null;
      count =
        (lib.foldl'
          (
            acc: a:
            if acc.leading && isSet a then
              {
                leading = true;
                n = acc.n + 1;
              }
            else
              {
                leading = false;
                inherit (acc) n;
              }
          )
          {
            leading = true;
            n = 0;
          }
          rest
        ).n;
      argv = lib.drop count rest;
      sets = map (s: {
        name = builtins.head (builtins.match "([^=]*)=.*" s);
        value = builtins.head (builtins.match "[^=]*=(.*)" s);
      }) (lib.take count rest);
      names = map (s: s.name) sets;
    in
    # The builder also holds the program's real path to the build: this is only what the words say.
    if
      argv == [ ]
      || !lib.hasPrefix "${out}/" (builtins.head argv)
      || builtins.elem ".." (lib.splitString "/" (builtins.head argv))
    then
      throw "bench/kernels/manifest.toml: workload ${w.name}'s `run` doesn't run a program under {build}"
    else if lib.length (lib.unique names) != lib.length names then
      throw "bench/kernels/manifest.toml: workload ${w.name}'s `run` sets a variable twice"
    else
      {
        env = builtins.listToAttrs sets;
        inherit argv;
      };

  # A check, as the builder runs it. A known-answers check is the manifest's commands, and the two files that say
  # how it came out: libsodium's tests write NAME.res where they run, to compare with the source's NAME.exp. The
  # manifest names the .exp, and where the .res goes is this file's to know.
  check =
    w: c:
    let
      what = "a check of workload ${w.name}";
      kind = need what "kind" c;
    in
    if kind == "known-answers" then
      let
        expected =
          lib.findFirst (lib.hasSuffix ".exp") (throw "bench/kernels/manifest.toml: ${what} names no .exp")
            (need what "test" c);
      in
      {
        inherit kind;
        run = map command (need what "run" c);
        expected = "${src}/${expected}";
        result = "${out}/${lib.removeSuffix ".exp" expected}.res";
      }
    else if kind == "output" then
      # The builder hashes a run's standard output, and nothing else.
      if (c.run or [ ]) != [ ] then
        throw "bench/kernels/manifest.toml: ${what} runs a separate output check, which the builder cannot execute"
      else if need what "output" c != [ "stdout" ] then
        throw "bench/kernels/manifest.toml: ${what} checks an output a build doesn't hash"
      else
        {
          inherit kind;
          sha256 = need what "sha256" c;
        }
    else
      throw "bench/kernels/manifest.toml: ${what} is of kind `${kind}`, which a build doesn't know";
  workloads = map (
    w:
    if (w.setup or [ ]) != [ ] then
      throw "bench/kernels/manifest.toml: workload ${w.name} needs setup commands, which the builder cannot execute"
    else
      {
        name = need "a workload" "name" w;
        build = map command (need "workload ${w.name}" "build" w);
        checks = map (check w) (need "workload ${w.name}" "check" w);
        run = launch w;
      }
  ) (entry "workload" p);

  configure = command (entry "configure" p);
  units = map (u: "${src}/${need "a unit" "source" u}") (entry "unit" p);

  # `replace` maps an object's path under the build to the IR it's made from. `checkEnv` is for the tests: what a
  # known-answers check's commands see besides the build's environment.
  variant =
    {
      name,
      replace ? { },
      checkEnv ? { },
    }:
    stdenv.mkDerivation {
      name = "kernels-libsodium-${name}";
      # The plan is this derivation's own attribute, so `placeholder "out"` in it is this derivation's output.
      plan = builtins.toJSON {
        inherit
          cc
          replace
          workloads
          attempt
          ;
        check_env = checkEnv;
        inherit configure units;
      };
      passAsFile = [ "plan" ];
      dontUnpack = true;
      # Stock clang, as bench/kernels/profile.sh has it: no hardening flags, and -m flags allowed.
      hardeningDisable = [ "all" ];
      env.NIX_ENFORCE_NO_NATIVE = "0";
      nativeBuildInputs = [
        pkgs.llvmPackages_latest.llvm
        pkgs.procps
        pkgs.python3
      ];
      dontStrip = true;
      dontPatchELF = true;
      dontFixup = true;
      buildPhase = ''
        python3 -I ${repo}/bench/kernels/kernels.py check
        mkdir -p $out
        python3 -I ${repo}/bench/kernels/builder.py "$planPath"
      '';
      installPhase = "true";
      # What bench/kernels/variants.py holds a build's evidence to, from here and not from the build: the objects
      # the table names, and each workload's checks.
      # Forcing the whole plan first, so a manifest a build can't follow doesn't evaluate.
      # Its words name the output by its placeholder, which variants.py fills in with the path realized.
      passthru.planned = builtins.deepSeq [ configure units workloads ] {
        inherit out;
        inherit replace attempt;
        table = builtins.attrNames replace;
        build = [
          configure
          [ "make" ]
        ]
        ++ lib.concatMap (w: w.build) workloads;
        workloads = map (w: {
          inherit (w) name run;
          checks = map (c: { inherit (c) run expected result; }) (
            builtins.filter (c: c.kind == "known-answers") w.checks
          );
          outputs = map (c: c.sha256) (builtins.filter (c: c.kind == "output") w.checks);
        }) workloads;
      };
    };

  baseline = variant { name = "baseline"; };
  # The IR the baseline's build captured for an object, and a copy of it with one piece of text replaced, which
  # fails if the text isn't there.
  captured = object: "${baseline}/ir/src/libsodium/${object}.ll";
  mutated =
    name: object: old: new:
    pkgs.runCommand name { } ''
      cp ${captured object} $out
      chmod +w $out
      substituteInPlace $out --replace-fail ${lib.escapeShellArg old} ${lib.escapeShellArg new}
    '';
  # The two objects libtool compiles from a unit, and a table for both.
  both = dir: object: ir: {
    "src/libsodium/${dir}/.libs/${object}" = ir "${dir}/.libs/${object}";
    "src/libsodium/${dir}/${object}" = ir "${dir}/${object}";
  };
  argon = both "crypto_pwhash/argon2" "libavx512f_la-argon2-fill-block-avx512f.o";
  blake = both "crypto_generichash/blake2b/ref" "libavx2_la-blake2b-compress-avx2.o";
  wrongBlake = blake (o: mutated "wrong-blake2b.ll" o "splat (i64 1))" "splat (i64 2))");
in
assert lib.assertMsg (
  matchesPin llvm.llvm
  && matchesPin llvm.clang-unwrapped.libllvm
  && "llvmorg-${llvm.clang-unwrapped.version}" == manifest.corpus.llvm_tag
) "the build compiler does not match the corpus LLVM tag and source hash";
assert lib.assertMsg (
  builtins.isString attempt && builtins.match "[a-zA-Z0-9_-]+" attempt != null
) "a kernel build attempt must be a nonempty alphanumeric label (hyphen and underscore allowed)";
{
  forAttempt =
    label:
    import ./variants.nix {
      inherit pkgs repo;
      attempt = label;
    };
  libsodium = {
    inherit baseline;
    # tests/variants_builds.py's builds. Each takes its IR from the baseline's own, so none is committed.
    tests = {
      # Clang's own IR, through the same llc: a candidate that changes no code.
      roundtrip = variant {
        name = "roundtrip";
        replace = argon captured;
      };
      blake-roundtrip = variant {
        name = "blake-roundtrip";
        replace = blake captured;
      };
      # Wrong candidates, each replacing a unit whole: a row of Argon2's round rotated wrongly, which only the
      # shared library's check runs, and BLAKE2b's last rotation wrong, which the statically linked workload
      # runs too.
      wrong-argon = variant {
        name = "wrong-argon";
        replace = argon (
          o:
          mutated "wrong-argon2.ll" o "<8 x i32> <i32 3, i32 0, i32 1, i32 2, i32 7, i32 4, i32 5, i32 6>"
            "<8 x i32> <i32 0, i32 3, i32 1, i32 2, i32 7, i32 4, i32 5, i32 6>"
        );
      };
      wrong-blake = variant {
        name = "wrong-blake";
        replace = wrongBlake;
      };
      # The baseline, with Automake told to skip the known-answers test: `make check` then exits 0.
      skipped = variant {
        name = "skipped";
        checkEnv.LOG_COMPILER = "${pkgs.writeShellScript "skip-the-test" "exit 77"}";
      };
      # A partial check beside a genuine wrong workload output must never certify either verdict.
      partial = variant {
        name = "partial";
        replace = wrongBlake;
        checkEnv.LOG_COMPILER = "${pkgs.writeShellScript "incomplete-check" ''
          printf 12345 > pwhash_argon2id.res
          exit 1
        ''}";
      };
      # A table naming an object the build never compiles.
      unused = variant {
        name = "unused";
        replace."src/libsodium/no/such/object.o" =
          captured "crypto_pwhash/argon2/libavx512f_la-argon2-fill-block-avx512f.o";
      };
      # A table with one of a unit's two objects.
      half = variant {
        name = "half";
        replace = lib.filterAttrs (object: _: !lib.hasInfix "/.libs/" object) (argon captured);
      };
    };
  };
}
