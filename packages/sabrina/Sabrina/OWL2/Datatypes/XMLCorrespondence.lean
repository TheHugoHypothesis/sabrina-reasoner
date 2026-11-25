import Sabrina.OWL2.SROIQD.Termination.XMLLiteralValidation

/-! Independent W3C XML 1.0 + Namespaces in XML 1.0 + Exclusive XML Canonicalization
    (Exc-C14N, https://www.w3.org/TR/xml-exc-c14n/) specification and correspondence
    theorems for SABRINA's `rdf:XMLLiteral` datatype (Milestone C.2.2). -/

namespace Sabrina.OWL2.Datatypes.XMLCorrespondence

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes

/-! ### 1. Independent W3C XML 1.0 + Exc-C14N Model -/

/-- Independent declarative XML 1.0 content node AST. -/
inductive XMLNode where
  | text (s : String)
  | elem (qname : String) (nsDecls : List (String × String)) (attrs : List (String × String)) (children : List XMLNode)
  | comment (body : String)
  | pi (target : String) (body : String)
  deriving Repr

private def escTextChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '\r' => ['&', '#', 'x', 'D', ';']
  | c => [c]

private def escText (s : String) : String :=
  String.ofList (s.toList.flatMap escTextChar)

private def escAttr (s : String) : String :=
  String.ofList <| s.toList.flatMap fun
    | '&' => ['&', 'a', 'm', 'p', ';']
    | '<' => ['&', 'l', 't', ';']
    | '"' => ['&', 'q', 'u', 'o', 't', ';']
    | '\t' => ['&', '#', 'x', '9', ';']
    | '\n' => ['&', '#', 'x', 'A', ';']
    | '\r' => ['&', '#', 'x', 'D', ';']
    | c => [c]

private def strLt (a b : String) : Bool :=
  a.toList.map Char.toNat < b.toList.map Char.toNat

private def sortByKey {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    let rec ins (a : α) : List α → List α
      | [] => [a]
      | y :: ys => if le a y then a :: y :: ys else y :: ins a ys
    ins x (sortByKey le xs)

/-- Independent W3C Exc-C14N §3 serialization of a balanced XML node list under
    current namespace scope `nsScope` and rendered ancestor scope `rendered`. -/
def renderExcC14NList (nsScope rendered : List (String × String)) : List XMLNode → String
  | [] => ""
  | n :: ns => renderExcC14NNode nsScope rendered n ++ renderExcC14NList nsScope rendered ns
where
  renderExcC14NNode (nsScope rendered : List (String × String)) : XMLNode → String
    | .text s => escText s
    | .comment body => "<!--" ++ body ++ "-->"
    | .pi target body =>
      if body.isEmpty then "<?" ++ target ++ "?>"
      else "<?" ++ target ++ " " ++ body ++ "?>"
    | .elem qname nsDecls attrs children =>
      let nsScope' := nsDecls ++ nsScope
      let elemPfx := match splitXMLQName qname with
        | some (some p, _) => p
        | _ => ""
      let attrEntries := attrs.map fun (aname, aval) =>
        match splitXMLQName aname with
        | some (some p, loc) => (aname, some p, (nsScope'.lookup p).getD "", loc, aval)
        | some (none, loc) => (aname, none, "", loc, aval)
        | none => (aname, none, "", aname, aval)
      let rawVis := (elemPfx :: attrEntries.filterMap fun (_, p?, _, _, _) => p?).eraseDups.filter (· != "xml")
      let toEmit := rawVis.filterMap fun p =>
        let uri := (nsScope'.lookup p).getD ""
        let prev := (rendered.lookup p).getD ""
        if p.isEmpty then
          if uri != prev then some ("", uri) else none
        else
          if rendered.lookup p != some uri then some (p, uri) else none
      let sortedNs := sortByKey (fun (p1, _) (p2, _) =>
        if p1.isEmpty then true
        else if p2.isEmpty then false
        else !strLt p2 p1) toEmit
      let rendered' := sortedNs ++ rendered
      let sortedAttrs := sortByKey (fun (_, _, u1, l1, _) (_, _, u2, l2, _) =>
        match u1.isEmpty, u2.isEmpty with
        | true, false => true
        | false, true => false
        | true, true => !strLt l2 l1
        | false, false => if u1 == u2 then !strLt l2 l1 else !strLt u2 u1) attrEntries
      let nsStr := String.join <| sortedNs.map fun (p, u) =>
        let nm := if p.isEmpty then "xmlns" else "xmlns:" ++ p
        " " ++ nm ++ "=\"" ++ escAttr u ++ "\""
      let attrStr := String.join <| sortedAttrs.map fun (qn, _, _, _, v) =>
        " " ++ qn ++ "=\"" ++ escAttr v ++ "\""
      "<" ++ qname ++ nsStr ++ attrStr ++ ">" ++
        renderExcC14NList nsScope' rendered' children ++
        "</" ++ qname ++ ">"

def initExcScope : List (String × String) :=
  [("", ""), ("xml", "http://www.w3.org/XML/1998/namespace")]

/-- Independent top-level W3C Exc-C14N serializer for balanced XML content. -/
def renderExcC14N (nodes : List XMLNode) : String :=
  renderExcC14NList initExcScope initExcScope nodes

/-! ### 2. Kernel-Checked Correspondence Proofs Against W3C Exc-C14N -/

private theorem escTextChar_of_simple {c : Char} (hc : isSimpleCanonTextChar c = true) :
    escTextChar c = [c] := by
  simp only [isSimpleCanonTextChar, Bool.and_eq_true, bne_iff_ne] at hc
  obtain ⟨⟨⟨⟨⟨_, hlt⟩, hgt⟩, hamp⟩, hcr⟩, _⟩ := hc
  unfold escTextChar
  split <;> first | rfl | exact (hamp rfl).elim | exact (hlt rfl).elim | exact (hgt rfl).elim | exact (hcr rfl).elim

private theorem flatMap_escTextChar_simple (cs : List Char)
    (h : ∀ c ∈ cs, isSimpleCanonTextChar c = true) :
    cs.flatMap escTextChar = cs := by
  induction cs with
  | nil => rfl
  | cons c tail ih =>
    rw [List.flatMap_cons, escTextChar_of_simple (h c (List.mem_cons_self ..)),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- Pure text node with simple XML 1.0 characters renders to a canonical fixed point
in SABRINA's `datatypeMap` for all inputs. -/
theorem renderExcC14N_simpleText_canonical (s : String)
    (hs : s.toList.all isSimpleCanonTextChar = true) :
    renderExcC14N [.text s] = s ∧
    checkCanonicalXMLLiteral (renderExcC14N [.text s]) = true ∧
    decodeLiteral ⟨renderExcC14N [.text s], rdf "XMLLiteral"⟩ = some (.xmlLiteral s) := by
  have hesc : escText s = s := by
    unfold escText
    rw [flatMap_escTextChar_simple s.toList (List.all_eq_true.mp hs), String.ofList_toList]
  have hout : renderExcC14N [.text s] = s := by
    simp [renderExcC14N, renderExcC14NList, renderExcC14NList.renderExcC14NNode, hesc]
  have hcanon : checkCanonicalXMLLiteral s = true := by
    simp [checkCanonicalXMLLiteral, canonicalizeXMLPass, hs]
  have hdec : decodeLiteral ⟨s, rdf "XMLLiteral"⟩ = some (.xmlLiteral s) :=
    (decodeXMLLiteral_iff s s).mpr ⟨rfl, hcanon⟩
  exact ⟨hout, hout.symm ▸ hcanon, hout.symm ▸ hdec⟩

theorem excC14N_empty_and_attr_sort :
    canonicalizeXMLLiteral "<a b='2' a='1'/>" =
      some (renderExcC14N [.elem "a" [] [("b", "2"), ("a", "1")] []]) := by decide

set_option maxHeartbeats 800000 in
theorem excC14N_prefixed_attr_uri_sort :
    canonicalizeXMLLiteral "<e xmlns:z=\"http://a.example\" xmlns:a=\"http://z.example\" a:k=\"1\" z:k=\"2\"/>" =
      some (renderExcC14N [.elem "e" [("z", "http://a.example"), ("a", "http://z.example")] [("a:k", "1"), ("z:k", "2")] []]) := by decide

theorem excC14N_visibly_utilized_ns_drop :
    canonicalizeXMLLiteral "<p:e xmlns:unused=\"http://unused.example\" xmlns:p=\"http://p.example\"/>" =
      some (renderExcC14N [.elem "p:e" [("unused", "http://unused.example"), ("p", "http://p.example")] [] []]) := by decide

theorem excC14N_ns_inheritance_and_undecl :
    canonicalizeXMLLiteral "<e xmlns=\"http://d.example\"><c xmlns=\"http://d.example\"><u xmlns=\"\"/></c></e>" =
      some (renderExcC14N [.elem "e" [("", "http://d.example")] []
        [.elem "c" [("", "http://d.example")] [] [.elem "u" [("", "")] [] []]]]) := by decide

theorem excC14N_cdata_and_escaping :
    canonicalizeXMLLiteral "<a><![CDATA[x < y & z > 0]]></a>" =
      some (renderExcC14N [.elem "a" [] [] [.text "x < y & z > 0"]]) := by decide

theorem excC14N_attr_whitespace_and_entities :
    canonicalizeXMLLiteral "<a k='x&#x9;y&#xA;\"z\"'/>" =
      some (renderExcC14N [.elem "a" [] [("k", "x\ty\n\"z\"")] []]) := by decide

theorem excC14N_comments_and_pi :
    canonicalizeXMLLiteral "<!-- note --><?app   val?><a/>" =
      some (renderExcC14N [.comment " note ", .pi "app" "val", .elem "a" [] [] []]) := by decide

theorem excC14N_normative_rejections :
    canonicalizeXMLLiteral "<e xmlns=\"relative/uri\"></e>" = none ∧
    canonicalizeXMLLiteral "<!-- bad -- comment -->" = none ∧
    canonicalizeXMLLiteral "<a>]]></a>" = none ∧
    canonicalizeXMLLiteral "<?xml version=\"1.0\"?><a/>" = none := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Combined normative W3C Exc-C14N correspondence suite. -/
theorem excC14N_normative_correspondence :
    canonicalizeXMLLiteral "<a b='2' a='1'/>" =
      some (renderExcC14N [.elem "a" [] [("b", "2"), ("a", "1")] []]) ∧
    canonicalizeXMLLiteral "<e xmlns:z=\"http://a.example\" xmlns:a=\"http://z.example\" a:k=\"1\" z:k=\"2\"/>" =
      some (renderExcC14N [.elem "e" [("z", "http://a.example"), ("a", "http://z.example")] [("a:k", "1"), ("z:k", "2")] []]) ∧
    canonicalizeXMLLiteral "<p:e xmlns:unused=\"http://unused.example\" xmlns:p=\"http://p.example\"/>" =
      some (renderExcC14N [.elem "p:e" [("unused", "http://unused.example"), ("p", "http://p.example")] [] []]) ∧
    canonicalizeXMLLiteral "<e xmlns=\"http://d.example\"><c xmlns=\"http://d.example\"><u xmlns=\"\"/></c></e>" =
      some (renderExcC14N [.elem "e" [("", "http://d.example")] []
        [.elem "c" [("", "http://d.example")] [] [.elem "u" [("", "")] [] []]]]) ∧
    canonicalizeXMLLiteral "<a><![CDATA[x < y & z > 0]]></a>" =
      some (renderExcC14N [.elem "a" [] [] [.text "x < y & z > 0"]]) ∧
    canonicalizeXMLLiteral "<a k='x&#x9;y&#xA;\"z\"'/>" =
      some (renderExcC14N [.elem "a" [] [("k", "x\ty\n\"z\"")] []]) ∧
    canonicalizeXMLLiteral "<!-- note --><?app   val?><a/>" =
      some (renderExcC14N [.comment " note ", .pi "app" "val", .elem "a" [] [] []]) ∧
    canonicalizeXMLLiteral "<e xmlns=\"relative/uri\"></e>" = none ∧
    canonicalizeXMLLiteral "<!-- bad -- comment -->" = none ∧
    canonicalizeXMLLiteral "<a>]]></a>" = none ∧
    canonicalizeXMLLiteral "<?xml version=\"1.0\"?><a/>" = none :=
  ⟨excC14N_empty_and_attr_sort, excC14N_prefixed_attr_uri_sort,
   excC14N_visibly_utilized_ns_drop, excC14N_ns_inheritance_and_undecl,
   excC14N_cdata_and_escaping, excC14N_attr_whitespace_and_entities,
   excC14N_comments_and_pi, excC14N_normative_rejections.1,
   excC14N_normative_rejections.2.1, excC14N_normative_rejections.2.2.1,
   excC14N_normative_rejections.2.2.2⟩

#print axioms renderExcC14N_simpleText_canonical
#print axioms excC14N_normative_correspondence

end Sabrina.OWL2.Datatypes.XMLCorrespondence
