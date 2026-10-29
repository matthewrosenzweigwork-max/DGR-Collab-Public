#!/usr/bin/env python3
"""Check distributed source identities. This does not run Lean or verify proofs."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
manifest = json.loads((here / "source-manifest.json").read_text())
root = here.parent / "lean"
for item in manifest["files"]:
    relative = Path(item["path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit("Invalid manifest path")
    path = root / relative
    if path.is_symlink():
        raise SystemExit("Unexpected source symlink: " + str(relative))
    data = path.read_bytes()
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if (blob != item["git_blob_sha1"] or
            hashlib.sha256(data).hexdigest() != item["sha256"] or
            len(data) != item["size"]):
        raise SystemExit("FAIL: " + str(relative))
print("PASS: exact source identities for", len(manifest["files"]), "files")
print("This is an integrity check, not a new proof certification.")
