#!/usr/bin/env python3
"""Group a macOS sample report; inclusive buckets overlap, exclusive ones do not."""
import argparse
import importlib.util
import json
from pathlib import Path
import re


def categories(kind):
    result = {
        "collection": lambda f: "initiate_collection" in f,
        "allocation": lambda f: any(word in f for word in
            ("runtime_alloc", "__gc__alloc", "__gc__buffer_new", "alloc_small", "try_cached_small_allocation")),
    }
    if kind == "encode":
        result.update({
            "output_buffer": lambda f: "std__bytes__Buffer__" in f or "std__mem__NativeBytes__" in f,
            "number_formatting": lambda f: "std__fmt__" in f or "std__string__Builder" in f,
            "encoder_events_and_strings": lambda f: "std__json__" in f or "std__encoding__" in f or "__bt_syn__encode__" in f,
        })
    else:
        result.update({
            "byte_cursor_and_whitespace": lambda f: bool(re.search(
                r"__(peekByte|takeByte|requiredByte|skipWhitespace|advance|advanceAscii|position|byteAt)__", f)),
            "parser_and_dom": lambda f: "std__json__parse" in f or bool(re.search(r"std__json__.*__parse__", f)),
            "typed_conversion": lambda f: "std__json__" in f or "std__encoding__" in f or "__bt_syn__decode__" in f,
            # Last, so phase totals do not override the finer exclusive buckets.
            "parse_phase_total": lambda f: "std__json__parseValue__" in f or bool(re.search(r"std__json__.*__parse__", f)),
            "typed_list_decode_total": lambda f: "std__encoding__List__" in f and "__decode__" in f,
        })
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kind", choices=["encode", "decode"], required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    helper = Path(__file__).resolve().parents[1] / "dictionary_ops/profile.py"
    spec = importlib.util.spec_from_file_location("sample_helper", helper)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    with args.input.open() as report:
        result = module.summarize(report, categories(args.kind))
    result["exclusive_percent"] = {key: 100 * value / result["samples"]
                                   for key, value in result["exclusive_priority_samples"].items()}
    result["method"] = ("Main-thread wall sampling, not hardware instruction counts. "
        "Exclusive ownership prioritizes collection, allocation, then named layers. "
        "Inclusive phase totals overlap other buckets. Inlined work belongs to its containing symbol.")
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("samples", "inclusive_percent", "exclusive_percent")}, indent=2))


if __name__ == "__main__":
    main()
