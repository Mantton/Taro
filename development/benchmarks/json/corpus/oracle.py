"""Structural oracle for downloaded, unique-key benchmark documents."""

import hashlib, json
from pathlib import Path


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate object key: {key!r}")
        result[key] = value
    return result


def shape(value):
    result = dict(
        objects=0,
        arrays=0,
        strings=0,
        numbers=0,
        booleans=0,
        nulls=0,
        utf8_bytes=0,
        depth=0,
        max_width=0,
    )

    def visit(v, depth):
        result["depth"] = max(result["depth"], depth)
        if isinstance(v, dict):
            result["objects"] += 1
            result["max_width"] = max(result["max_width"], len(v))
            for k, x in v.items():
                result["utf8_bytes"] += len(k.encode())
                visit(x, depth + 1)
        elif isinstance(v, list):
            result["arrays"] += 1
            for x in v:
                visit(x, depth + 1)
        elif isinstance(v, str):
            result["strings"] += 1
            result["utf8_bytes"] += len(v.encode())
        elif isinstance(v, bool):
            result["booleans"] += 1
        elif v is None:
            result["nulls"] += 1
        else:
            result["numbers"] += 1

    visit(value, 0)
    result["top"] = (
        len(value.encode())
        if isinstance(value, str)
        else len(value) if isinstance(value, (dict, list)) else 1
    )
    return result


def canada(value):
    assert set(value) == {"type", "features"} and value["type"] == "FeatureCollection"
    result = dict(
        features=len(value["features"]), rings=0, points=0, coordinates=0, float_sum=0.0
    )
    for feature in value["features"]:
        assert (
            set(feature) == {"type", "properties", "geometry"}
            and feature["type"] == "Feature"
        )
        assert (
            feature["properties"] == {"name": "Canada"}
            and feature["geometry"]["type"] == "Polygon"
        )
        assert set(feature["geometry"]) == {"type", "coordinates"}
        for ring in feature["geometry"]["coordinates"]:
            result["rings"] += 1
            for point in ring:
                assert len(point) == 2
                result["points"] += 1
                result["coordinates"] += len(point)
                for x in point:
                    result["float_sum"] += x
    return result


def prepare(cache, manifest):
    results = {}
    for item in manifest["files"]:
        data = (cache / (item["name"] + ".json")).read_bytes()
        assert (
            len(data) == item["bytes"]
            and hashlib.sha256(data).hexdigest() == item["sha256"]
        )
        value = json.loads(data, object_pairs_hook=unique_object)
        record = shape(value)
        if item["name"] == "canada":
            record["typed"] = canada(value)
        results[item["name"]] = record
        print(
            item["name"],
            record["top"],
            "top members,",
            record["max_width"],
            "maximum object width,",
            record["depth"],
            "depth",
            flush=True,
        )
        del value, data
    return results


if __name__ == "__main__":
    import sys

    manifest = json.loads(Path(__file__).with_name("fixtures.json").read_text())
    out = Path(sys.argv[1])
    records = prepare(out / "inputs", manifest)
    (out / "oracle.json").write_text(json.dumps(records, indent=2) + "\n")
