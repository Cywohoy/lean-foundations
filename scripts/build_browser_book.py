"""Build the book's exact wasm32 contexts using a matching native compiler.

Run in Linux/WSL; all output stays under the specified output directory.
The Ample library and browser runtime are inputs and are never modified.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from book_code import ROOT, CHAPTERS, export_module, translate

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean", type=Path, required=True)
parser.add_argument("--ample-lib", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=True)
env = {**os.environ, "LEAN_PATH": str(out) + os.pathsep + str(args.ample_lib.resolve())}

def compile_module(name, source):
    relative = Path(*name.split("."))
    file = out / relative.with_suffix(".lean")
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(source, encoding="utf-8")
    result = subprocess.run([str(args.lean.resolve()), "-o", str(relative.with_suffix(".olean")), str(relative.with_suffix(".lean"))],
                            cwd=out, env=env, capture_output=True, text=True, timeout=180)
    if result.returncode or "declaration uses `sorry`" in result.stdout:
        raise RuntimeError(name + "\n" + result.stdout + result.stderr)
    return [{"name": p.relative_to(out).as_posix(), "bytes": p.stat().st_size,
             "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in sorted(file.parent.glob(file.stem + ".*")) if p.suffix != ".lean"]

book_files = compile_module("AmpleBrowserContext.LearningGuard",
    (ROOT / "web/lean/LearningGuard.lean").read_text(encoding="utf-8"))
for chapter in CHAPTERS:
    book_files += compile_module("AmpleBrowserContext.Book." + chapter,
        export_module((ROOT / "AlgebraBook" / (chapter + ".lean")).read_text(encoding="utf-8")))
    print("Checked chapter " + chapter, flush=True)

manifest = json.loads((ROOT / "_out/html-multi/playground.json").read_text(encoding="utf-8"))
prefixes = {hashlib.sha256(translate(v["before"]).encode()).hexdigest(): translate(v["before"])
            for v in manifest.values() if v.get("exercise")}

def context(digest, source):
    scopes, commands = [], []
    lines = source.splitlines()
    for index,line in enumerate(lines):
        opening = re.fullmatch(r"(namespace|section)(?:\s+(\S+))?\s*",line)
        if opening: scopes.append(opening[2] or "")
        elif re.fullmatch(r"end(?:\s+\S+)?\s*", line) and scopes: scopes.pop()
        if (re.match(r"^(?:namespace|section|end|open|variable|set_option|noncomputable section|local (?:notation|infixr?|prefix|postfix|attribute))\b",line)
                and not line.rstrip().endswith(" in")):
            commands.append(line)
            for continuation in lines[index+1:]:
                if continuation and not continuation[0].isspace(): break
                commands.append(continuation)
    name = "AmpleBrowserContext.C" + digest[:24]
    closed = source + "\n" + "".join("end" + (" " + s if s else "") + "\n" for s in reversed(scopes))
    files = compile_module(name, closed)
    return digest, {"module": name, "scope": "\n".join(commands), "files": book_files + files}

contexts={}
with ThreadPoolExecutor(max_workers=3) as pool:
    for future in as_completed([pool.submit(context,*p) for p in prefixes.items()]):
        digest, data = future.result()
        contexts[digest]=data
        print(f"Checked context {len(contexts)}/{len(prefixes)}",flush=True)
(out/"contexts.json").write_text(json.dumps(contexts,indent=2)+"\n",encoding="utf-8")
print(f"Checked all {len(contexts)} distinct exercise contexts.",flush=True)
