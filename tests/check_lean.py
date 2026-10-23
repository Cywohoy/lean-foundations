"""Check exported chapter code and regenerated exercises."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import subprocess, hashlib
root=Path(__file__).resolve().parents[1]
def fingerprint():
    return {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/"Exercises").rglob("*") if p.is_file()}
before=fingerprint()
paths=sorted((root/"_out/example-code").rglob("*.lean"))
paths+=sorted((root/"ExerciseTemplates").glob("*.lean"))
assert paths,"Build the book first"
def run(path):
    result=subprocess.run(["lake","env","lean",str(path)],cwd=root,capture_output=True,text=True,encoding="utf-8")
    return path,result
fail=[]
with ThreadPoolExecutor(max_workers=3) as pool:
    for future in as_completed([pool.submit(run,p) for p in paths]):
        path,result=future.result()
        if result.returncode:
            fail.append(path)
            print(path.relative_to(root),result.stdout,result.stderr,flush=True)
assert before==fingerprint(),"Personal solutions changed"
print(f"Checked {len(paths)} Lean files; {len(fail)} failures.",flush=True)
raise SystemExit(bool(fail))
