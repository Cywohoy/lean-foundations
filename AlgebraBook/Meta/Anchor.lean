import VersoManual

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean
open Verso.Output.TeX

namespace AlgebraBook

-- A stable reference target within a paragraph, without adding a TOC entry.
inline_extension Inline.anchor (tag : String) where
  data := .str tag
  traverse id data _ := do
    let .ok tag := data.getStr? | return none
    let _ ← providedTag id (← read).path tag
    let title := (← read).headers.back?.map (·.titleString)
    modify fun st => st.saveDomainObject sectionDomain tag id
      |>.saveDomainObjectData sectionDomain tag (json%{
        "title": $title, "shortTitle": null, "sectionNum": null,
        "context": [], "searchPriority": 0
      })
    return none
  toHtml :=
    open Verso.Output.Html in
    some fun go id _ contents => do
      let some link := (← read).traverseState.externalTags.get? id
        | return ← contents.mapM go
      return {{<span id={{link.htmlId.toString}}>{{← contents.mapM go}}</span>}}
  toTeX := some fun go id _ contents => do
    let some link := (← Verso.Doc.TeX.state).externalTags.get? id
      | return ← contents.mapM go
    return .seq #[.raw ("\\label{" ++ labelForTeX link.htmlId ++ "}"), ← contents.mapM go]

structure AnchorArgs where
  tag : String

meta instance : FromArgs AnchorArgs DocElabM where
  fromArgs := AnchorArgs.mk <$> .positional `tag .string

@[role]
meta def anchor : RoleExpanderOf AnchorArgs
  | {tag}, content => do
    let content ← content.mapM elabInline
    ``(Inline.other (Inline.anchor $(quote tag)) #[$content,*])

end AlgebraBook
