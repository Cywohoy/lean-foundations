"""Add checked book contexts to the pinned runtime without changing its library."""
from pathlib import Path
import argparse, hashlib, io, json, tarfile

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--base",type=Path,required=True)
parser.add_argument("--url",help="Public URL for the resulting book runtime")
parser.add_argument("--contexts",type=Path,required=True)
parser.add_argument("--output",type=Path,required=True)
parser.add_argument("--config",type=Path,required=True)
args=parser.parse_args()
root=Path(__file__).resolve().parents[1]
pin=json.loads((root/"web/wasm-base-runtime.json").read_text())
assert hashlib.file_digest(args.base.open("rb"),"sha256").hexdigest()==pin["sha256"],"Base runtime does not match the public pin"
contexts=json.loads((args.contexts/"contexts.json").read_text())
files={item["name"]:item for c in contexts.values() for item in c["files"]}
for name,meta in files.items():
    assert hashlib.sha256((args.contexts/name).read_bytes()).hexdigest()==meta["sha256"],name
args.output.parent.mkdir(parents=True,exist_ok=True)
with tarfile.open(args.base) as old, tarfile.open(args.output,"w:gz",compresslevel=3) as new:
    for member in old:
        if member.name=="contexts.json" or member.name.startswith("contexts/"):continue
        new.addfile(member,old.extractfile(member) if member.isfile() else None)
    data=json.dumps(contexts).encode()
    entry=tarfile.TarInfo("contexts.json");entry.size=len(data)
    new.addfile(entry,io.BytesIO(data))
    for name in files:
        new.add(args.contexts/name,arcname="contexts/"+name)
with args.output.open("rb") as stream: digest=hashlib.file_digest(stream,"sha256").hexdigest()
args.config.write_text(json.dumps({**pin,"url": args.url or pin["url"],"file":str(args.output.resolve()),"sha256":digest,
    "bytes":args.output.stat().st_size,"bookContexts":len(contexts)},indent=2)+"\n")
print(f"Packaged {len(contexts)} contexts: {args.output}")
