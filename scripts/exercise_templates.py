"""Regenerate exercise templates without touching any personal solution file."""
from pathlib import Path
import re
from book_code import ROOT, CHAPTERS

target=ROOT/"ExerciseTemplates"
target.mkdir(exist_ok=True)
for chapter in CHAPTERS:
    source=(ROOT/"AlgebraBook"/(chapter+".lean")).read_text(encoding="utf-8")
    chunks=[]
    for flags,code in re.findall(r"```savedLean([^\n]*)\n(.*?)```",source,re.S):
        if "-keep" in flags and re.search(r"\bsorry\b",code):
            chunks.append(code.strip())
    scopes="open scoped Ample Classical\n"
    if chapter=="Proof":
        scopes+="open IntroExamples ProofExamples\n"
    else:
        scopes+="open scoped Ample.Auto\n"
        scopes+="open Ample\nlocal infixr:90 (priority := high) \" ∘ \" => Ample.compose\n"
    if chapter=="NumbersRelations":
        scopes+='local infix:50 (priority := high) " ∣ " => Ample.Divides\n'
        scopes+='local notation:50 a " ≡ " b " [ZMOD " n "]" => Ample.Congruent n a b\n'
    code=f"import AlgebraBook.{chapter}\n\n{scopes}\nnamespace Exercises.{chapter}\n\n"
    code+="\n\n".join(chunks)+f"\n\nend Exercises.{chapter}\n"
    (target/(chapter+".lean")).write_text(code,encoding="utf-8")
# Only remove obsolete generated templates in this new project's template directory.
# Exercises/ is deliberately never read, copied or written here.
for file in target.glob("*.lean"):
    if file.stem not in CHAPTERS:
        assert file.resolve().parent==target.resolve()
        file.unlink()
print("Generated four chapter templates; personal solutions untouched.")
