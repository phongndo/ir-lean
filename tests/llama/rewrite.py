#!/usr/bin/env python3
"""Recognize the exact optimized q5_0 bit-unpack DAG and expose the i32 mask.

This exploratory matcher accepts only the fixed six-instruction DAG present in
the real optimized llama.cpp q5_0 kernel. It preserves original producers and
rewrites the final select; their other uses are untouched. Debug and unrelated
metadata remain attached. Changed local use-list directives are omitted because
they describe serialization order rather than program behavior.

The CLI requires an explicit little-endian layout and exactly three sites in
ggml_vec_dot_q5_0_q8_0 unless --function and --expect-sites override the contract.
Only debug metadata is accepted on matched instructions. The pure helper is
emitted from the extracted and renamed instructions; each site's normalized
source and replacement must agree. TARGET.witness.json records those DAGs and
the source, target, helper, matcher and canonical witness SHA-256 hashes. Supply
--helpers-dir to write the helper as a separate file as well as in the witness.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path

SSA = r"%[-a-zA-Z$._0-9]+"
ASSIGN = re.compile(r"  (" + SSA + r") = (.*)")
SHUFFLE = "<" + ", ".join(f"i32 {i // 8}" for i in range(32)) + ">"
COMPLEMENT = "<" + ", ".join(f"i8 {((255 ^ (1 << (i % 8))) + 128) % 256 - 128}" for i in range(32)) + ">"
SELECT_SUFFIX = ", <32 x i8> zeroinitializer, <32 x i8> splat (i8 -16)"
DEFAULT_FUNCTION = "ggml_vec_dot_q5_0_q8_0"


def separate_metadata(body):
    parts = body.split(", !", 1)
    return parts[0], (", !" + parts[1]) if len(parts) == 2 else ""


def module_layout(text):
    layouts = re.findall(r'^target datalayout = "([^"]*)"$', text, re.MULTILINE)
    if (
        len(layouts) != 1
        or layouts[0].split("-")[0] != "e"
        or [part for part in layouts[0].split("-") if part in {"e", "E"}] != ["e"]
    ):
        raise ValueError("requires one explicit little-endian target datalayout beginning with e")
    triples = re.findall(r'^target triple = "([^"]*)"$', text, re.MULTILINE)
    if len(triples) != 1:
        raise ValueError("requires one explicit target triple")
    return layouts[0], triples[0]


def normalize_dag(lines, names):
    """Rename actual extracted instructions; do not reconstruct their operations."""
    normalized = []
    for line in lines:
        body, _ = separate_metadata(line)

        def rename(match):
            name = match.group(0)
            if name not in names:
                raise ValueError(f"unexpected free SSA value in extracted DAG: {name}")
            return names[name]

        normalized.append(re.sub(SSA, rename, body))
    return normalized


def helper_ir(layout, triple, sites):
    if not sites:
        raise ValueError("cannot emit helper without a matched source DAG")
    source = sites[0]["normalized_source"]
    target = sites[0]["normalized_target"]
    if any(site["normalized_source"] != source or site["normalized_target"] != target for site in sites):
        raise ValueError("matched sites do not normalize to the same extracted helper")
    return f'''target datalayout = "{layout}"
target triple = "{triple}"

define <32 x i8> @src(i32 %x) {{
entry:
{chr(10).join(source)}
  ret <32 x i8> %out
}}

define <32 x i8> @tgt(i32 %x) {{
entry:
{chr(10).join(target)}
  ret <32 x i8> %out
}}
'''


def rewrite(text, allowed_functions):
    module_layout(text)
    if not allowed_functions:
        raise ValueError("at least one explicitly selected function is required")
    definitions, original_lines = {}, {}
    function, out, sites = "", [], []
    changed_users = {}
    for line in text.splitlines():
        if line.startswith("define "):
            function_match = re.search(r"@([^ (]+)", line)
            if function_match is None:
                raise ValueError("cannot parse function name")
            function = function_match.group(1)
            definitions, original_lines, changed_users = {}, {}, {}
        if line == "}":
            function = ""
            definitions, original_lines, changed_users = {}, {}, {}
        order = re.fullmatch(r"\s*uselistorder (.+), \{[^{}]+\}", line)
        if order:
            local = re.search(r"(" + SSA + r")$", order.group(1))
            affected = changed_users.get(local.group(1)) if local else None
            if affected is not None:
                sites[affected]["dropped_uselistorders"].append(line)
                continue
        assigned = ASSIGN.fullmatch(line)
        if assigned:
            name, attached_body = assigned.groups()
            body, metadata = separate_metadata(attached_body)
            definitions[name] = body
            original_lines[name] = line
            select = re.fullmatch(r"select <32 x i1> (" + SSA + r")" + re.escape(SELECT_SUFFIX), body)
            if select and function in allowed_functions:
                mask = select.group(1)
                cmp = re.fullmatch(
                    r"icmp eq <32 x i8> (" + SSA + r"), splat \(i8 -1\)", definitions.get(mask, "")
                )
                if not cmp:
                    out.append(line)
                    continue
                or_name = cmp.group(1)
                or_inst = re.fullmatch(
                    r"or <32 x i8> (" + SSA + r"), " + re.escape(COMPLEMENT), definitions.get(or_name, "")
                )
                if not or_inst:
                    out.append(line)
                    continue
                shuffle_name = or_inst.group(1)
                shuffle = re.fullmatch(
                    r"shufflevector <32 x i8> ("
                    + SSA
                    + r"), <32 x i8> poison, <32 x i32> "
                    + re.escape(SHUFFLE),
                    definitions.get(shuffle_name, ""),
                )
                if not shuffle:
                    out.append(line)
                    continue
                bytes_name = shuffle.group(1)
                bitcast = re.fullmatch(
                    r"bitcast <8 x i32> (" + SSA + r") to <32 x i8>", definitions.get(bytes_name, "")
                )
                if not bitcast:
                    out.append(line)
                    continue
                insert_name = bitcast.group(1)
                insert = re.fullmatch(
                    r"insertelement <8 x i32> poison, i32 (" + SSA + r"), i64 0",
                    definitions.get(insert_name, ""),
                )
                if not insert:
                    out.append(line)
                    continue
                operand = insert.group(1)
                tag = f"%irlean.bitspread.{len(sites)}"
                if tag in text:
                    raise ValueError(f"fresh SSA prefix already appears: {tag}")
                dbg = re.search(r", !dbg !\d+", metadata)
                location = dbg.group(0) if dbg else ""
                replacement = [
                    f"  {tag}.mask = bitcast i32 {operand} to <32 x i1>{location}",
                    f"  {name} = select <32 x i1> {tag}.mask{SELECT_SUFFIX}{metadata}",
                ]
                original = [
                    original_lines[x] for x in (insert_name, bytes_name, shuffle_name, or_name, mask, name)
                ]
                if any(
                    not re.fullmatch(r"(?:, !dbg !\d+)?", separate_metadata(item)[1]) for item in original
                ):
                    out.append(line)
                    continue
                normalized_source = normalize_dag(
                    original,
                    {
                        operand: "%x",
                        insert_name: "%insert",
                        bytes_name: "%bytes",
                        shuffle_name: "%shuffle",
                        or_name: "%or",
                        mask: "%mask",
                        name: "%out",
                    },
                )
                normalized_target = normalize_dag(
                    replacement, {operand: "%x", tag + ".mask": "%mask", name: "%out"}
                )
                changed_users[operand] = len(sites)
                changed_users[mask] = len(sites)
                sites.append(
                    {
                        "function": function,
                        "input": operand,
                        "result": name,
                        "helper": "q5_bitspread.ll",
                        "original": original,
                        "replacement": replacement,
                        "normalized_source": normalized_source,
                        "normalized_target": normalized_target,
                        "dropped_uselistorders": [],
                    }
                )
                out.extend(replacement)
                continue
        out.append(line)
    return "\n".join(out) + "\n", sites


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def prepare(source_bytes, allowed_functions, expected_sites):
    """Validate the complete transformation before writing any output artifact."""
    if expected_sites < 1:
        raise ValueError("expected site count must be positive")
    text = source_bytes.decode("utf-8")
    layout, triple = module_layout(text)
    result, sites = rewrite(text, allowed_functions)
    matched_functions = {site["function"] for site in sites}
    if len(sites) != expected_sites:
        raise ValueError(f"expected exactly {expected_sites} rewrite sites, found {len(sites)}")
    if matched_functions != allowed_functions:
        raise ValueError(
            f"matched function set {sorted(matched_functions)} differs from selected functions "
            f"{sorted(allowed_functions)}"
        )
    helper = helper_ir(layout, triple, sites)
    witness = {
        "schema": "ir-lean-q5-bitspread-witness-v1",
        "selected_functions": sorted(allowed_functions),
        "expected_sites": expected_sites,
        "actual_sites": len(sites),
        "data_layout": layout,
        "target_triple": triple,
        "source_sha256": sha256(source_bytes),
        "target_sha256": sha256(result.encode("utf-8")),
        "helper_sha256": sha256(helper.encode("utf-8")),
        "helper_ir": helper,
        "normalized_source_sha256": sha256(canonical_json(sites[0]["normalized_source"])),
        "normalized_target_sha256": sha256(canonical_json(sites[0]["normalized_target"])),
        "sites": sites,
    }
    return result, helper, witness


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    parser.add_argument(
        "--function", action="append", help=f"exact function allowlist; default: {DEFAULT_FUNCTION}"
    )
    parser.add_argument(
        "--expect-sites", type=int, default=3, help="exact total number of accepted sites (default: 3)"
    )
    parser.add_argument("--helpers-dir", type=Path)
    parser.add_argument("--witness", type=Path, help="witness JSON path; default: TARGET.witness.json")
    args = parser.parse_args()
    functions = args.function or [DEFAULT_FUNCTION]
    if len(functions) != len(set(functions)):
        parser.error("duplicate --function selection")
    witness_path = args.witness or args.target.with_suffix(args.target.suffix + ".witness.json")
    helper_path = args.helpers_dir / "q5_bitspread.ll" if args.helpers_dir else None
    paths = [args.source, args.target, witness_path] + ([helper_path] if helper_path else [])
    if len({path.resolve() for path in paths}) != len(paths):
        parser.error("source, target, helper and witness paths must be distinct")
    try:
        result, helper, witness = prepare(args.source.read_bytes(), set(functions), args.expect_sites)
    except (ValueError, UnicodeError) as error:
        parser.error(str(error))
    witness.update(
        {
            "source_path": str(args.source),
            "target_path": str(args.target),
            "helper_path": str(helper_path) if helper_path else None,
            "matcher_sha256": sha256(Path(__file__).read_bytes()),
            "witness_hash_rule": "SHA-256 of canonical sorted compact JSON with witness_sha256 omitted",
        }
    )
    witness["witness_sha256"] = sha256(canonical_json(witness))
    args.target.write_bytes(result.encode("utf-8"))
    if helper_path:
        helper_path.parent.mkdir(parents=True, exist_ok=True)
        helper_path.write_bytes(helper.encode("utf-8"))
    witness_path.write_text(json.dumps(witness, indent=2) + "\n")
    print(json.dumps(witness, indent=2))


if __name__ == "__main__":
    main()
