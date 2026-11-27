#!/usr/bin/env python3
"""W3C OWL 2 DL Conformance Test Suite Gate for SABRINA.

Exercises `sabrina-query --strict-owl2dl` and `sabrina-session` across all
normative W3C OWL 2 DL conformance categories:
  1. Consistency & Inconsistency (FSS, RDF/XML, Turtle)
  2. Positive Entailment (class, property, chain, n-ary, nominal, blank-node)
  3. Negative Entailment / Open-World Independence
  4. W3C OWL 2 Datatype Map & Facets (owl:real, IEEE-754, dateTimeStamp,
     XSD 1.1 Unicode regex, Exc-C14N rdf:XMLLiteral, RDF/Turtle restrictions)
  5. Strict W3C §5.8.2 & §11.2 Non-DL Syntax Rejection & Legal Punning
  6. Cross-Syntax Multi-Document Import Closure (RDF/XML importing Turtle)
  7. Certified TBox Classification, ABox Realization & Session Server.

Exits 0 iff 100% of conformance tests pass.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]
QUERY_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "sabrina-query"
SESSION_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "sabrina-session"
T1_PATH = REPO_ROOT / "counterexamples" / "T1_acyclic_valid_owl2dl.ofn"


def run_query(
    payload: List[Any], *, strict: bool = True, timeout: float = 30.0
) -> Tuple[int, Dict[str, Any]]:
    cmd = [str(QUERY_BIN)]
    if strict:
        cmd.append("--strict-owl2dl")
    proc = subprocess.run(
        cmd,
        input=json.dumps(payload),
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    if not proc.stdout.strip():
        raise RuntimeError(f"sabrina-query returned empty output (rc={proc.returncode}): {proc.stderr}")
    return proc.returncode, json.loads(proc.stdout)


RDFXML_BIO = """<?xml version="1.0"?>
<!DOCTYPE rdf:RDF [
  <!ENTITY ex "http://example.org/bio#">
  <!ENTITY owl "http://www.w3.org/2002/07/owl#">
]>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:ex="http://example.org/bio#"
         xml:base="http://example.org/bio">
  <owl:Ontology rdf:about="http://example.org/bio"/>
  <owl:Class rdf:about="&ex;Animal"/>
  <owl:Class rdf:about="&ex;Mammal">
    <rdfs:subClassOf rdf:resource="&ex;Animal"/>
  </owl:Class>
  <owl:Class rdf:about="&ex;Dog">
    <rdfs:subClassOf rdf:resource="&ex;Mammal"/>
  </owl:Class>
  <owl:Class rdf:about="&ex;Cat">
    <rdfs:subClassOf rdf:resource="&ex;Mammal"/>
    <owl:disjointWith rdf:resource="&ex;Dog"/>
  </owl:Class>
  <owl:ObjectProperty rdf:about="&ex;parentOf"/>
  <owl:ObjectProperty rdf:about="&ex;ancestorOf">
    <rdf:type rdf:resource="&owl;TransitiveProperty"/>
    <owl:propertyChainAxiom rdf:parseType="Collection">
      <rdf:Description rdf:about="&ex;parentOf"/>
      <rdf:Description rdf:about="&ex;ancestorOf"/>
    </owl:propertyChainAxiom>
  </owl:ObjectProperty>
  <owl:NamedIndividual rdf:about="&ex;fido">
    <rdf:type rdf:resource="&ex;Dog"/>
  </owl:NamedIndividual>
  <owl:NamedIndividual rdf:about="&ex;milo">
    <rdf:type rdf:resource="&ex;Mammal"/>
  </owl:NamedIndividual>
</rdf:RDF>
"""

TURTLE_ORG = """
@prefix : <http://example.org/org#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

<http://example.org/org> a owl:Ontology .

:Person a owl:Class .
:Human a owl:Class ; owl:equivalentClass :Person .
:Employee a owl:Class ; rdfs:subClassOf :Person .
:Manager a owl:Class ;
  owl:equivalentClass [
    a owl:Class ;
    owl:intersectionOf ( :Employee [ a owl:Restriction ; owl:onProperty :manages ; owl:someValuesFrom :Person ] )
  ] .
:Ghost a owl:Class ;
  rdfs:subClassOf :Employee , [ a owl:Class ; owl:complementOf :Person ] .

:manages a owl:ObjectProperty ;
  rdfs:domain :Employee ;
  rdfs:range :Person .

:alice a owl:NamedIndividual , :Employee ;
  :manages :bob .
:bob a owl:NamedIndividual , :Person .
"""


def build_cases() -> List[Dict[str, Any]]:
    t1_ofn = T1_PATH.read_text(encoding="utf-8")
    return [
        # --- 1. Consistency & Inconsistency ---
        {
            "id": "Consistent-001-RDFXML-Bio",
            "payload": ["sabrina-ofn-query-v1", "c1", RDFXML_BIO],
            "expect_verdict": "SATISFIABLE",
            "expect_verified": True,
        },
        {
            "id": "Inconsistent-001-RDFXML-DisjointClash",
            "payload": [
                "sabrina-ofn-query-v1",
                "ic1",
                """<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:ex="http://example.org/c#">
  <owl:Ontology rdf:about="http://example.org/c"/>
  <owl:Class rdf:about="http://example.org/c#A"/>
  <owl:Class rdf:about="http://example.org/c#B">
    <owl:disjointWith rdf:resource="http://example.org/c#A"/>
  </owl:Class>
  <owl:Class rdf:about="http://example.org/c#C">
    <rdfs:subClassOf rdf:resource="http://example.org/c#A"/>
    <rdfs:subClassOf rdf:resource="http://example.org/c#B"/>
  </owl:Class>
  <owl:NamedIndividual rdf:about="http://example.org/c#x">
    <rdf:type rdf:resource="http://example.org/c#C"/>
  </owl:NamedIndividual>
</rdf:RDF>""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Inconsistent-002-Turtle-FunctionalAllDifferent",
            "payload": [
                "sabrina-ofn-query-v1",
                "ic2",
                """@prefix : <http://example.org/f#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
<http://example.org/f> a owl:Ontology .
:hasMother a owl:ObjectProperty , owl:FunctionalProperty .
:a a owl:NamedIndividual ; :hasMother :m1 , :m2 .
:m1 a owl:NamedIndividual .
:m2 a owl:NamedIndividual .
[ a owl:AllDifferent ; owl:members ( :m1 :m2 ) ] .
""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Inconsistent-003-FSS-T1-BoundaryCounterexample",
            "payload": ["sabrina-ofn-query-v1", "ic3", t1_ofn],
            "strict": False,
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Consistent-002-RDFXML-InverseFunctionalMerge",
            "payload": [
                "sabrina-ofn-query-v1",
                "c2",
                """<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:ex="http://example.org/ifp#">
  <owl:Ontology rdf:about="http://example.org/ifp"/>
  <owl:ObjectProperty rdf:about="http://example.org/ifp#ssn">
    <rdf:type rdf:resource="http://www.w3.org/2002/07/owl#InverseFunctionalProperty"/>
  </owl:ObjectProperty>
  <owl:NamedIndividual rdf:about="http://example.org/ifp#a">
    <ex:ssn rdf:resource="http://example.org/ifp#id1"/>
  </owl:NamedIndividual>
  <owl:NamedIndividual rdf:about="http://example.org/ifp#b">
    <ex:ssn rdf:resource="http://example.org/ifp#id1"/>
  </owl:NamedIndividual>
  <owl:NamedIndividual rdf:about="http://example.org/ifp#id1"/>
</rdf:RDF>""",
                "Prefix(ex:=<http://example.org/ifp#>) SameIndividual(ex:a ex:b)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "Inconsistent-004-RDFXML-IrreflexiveHasSelf",
            "payload": [
                "sabrina-ofn-query-v1",
                "ic4",
                """<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:xsd="http://www.w3.org/2001/XMLSchema#"
         xmlns:ex="http://example.org/self#">
  <owl:Ontology rdf:about="http://example.org/self"/>
  <owl:ObjectProperty rdf:about="http://example.org/self#r">
    <rdf:type rdf:resource="http://www.w3.org/2002/07/owl#IrreflexiveProperty"/>
  </owl:ObjectProperty>
  <owl:NamedIndividual rdf:about="http://example.org/self#a">
    <rdf:type>
      <owl:Restriction>
        <owl:onProperty rdf:resource="http://example.org/self#r"/>
        <owl:hasSelf rdf:datatype="http://www.w3.org/2001/XMLSchema#boolean">true</owl:hasSelf>
      </owl:Restriction>
    </rdf:type>
  </owl:NamedIndividual>
</rdf:RDF>""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Inconsistent-005-Turtle-AsymmetricClash",
            "payload": [
                "sabrina-ofn-query-v1",
                "ic5",
                """@prefix : <http://example.org/asym#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
<http://example.org/asym> a owl:Ontology .
:lt a owl:ObjectProperty , owl:AsymmetricProperty .
:a a owl:NamedIndividual ; :lt :b .
:b a owl:NamedIndividual ; :lt :a .
""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Inconsistent-006-FSS-HasKeyMixedClash",
            "payload": [
                "sabrina-ofn-query-v1",
                "ic6",
                """Prefix(:=<http://example.org/key#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/key>
  Declaration(Class(:Person))
  Declaration(ObjectProperty(:org))
  Declaration(DataProperty(:empId))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  Declaration(NamedIndividual(:acme))
  HasKey(:Person (:org) (:empId))
  ClassAssertion(:Person :a)
  ClassAssertion(:Person :b)
  ObjectPropertyAssertion(:org :a :acme)
  ObjectPropertyAssertion(:org :b :acme)
  DataPropertyAssertion(:empId :a "101"^^xsd:integer)
  DataPropertyAssertion(:empId :b "101"^^xsd:integer)
  DifferentIndividuals(:a :b)
)""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Consistent-003-RDFXML-DisjointUnion",
            "payload": [
                "sabrina-ofn-query-v1",
                "c3",
                """<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:ex="http://example.org/du#">
  <owl:Ontology rdf:about="http://example.org/du"/>
  <owl:Class rdf:about="http://example.org/du#Bit">
    <owl:disjointUnionOf rdf:parseType="Collection">
      <rdf:Description rdf:about="http://example.org/du#Zero"/>
      <rdf:Description rdf:about="http://example.org/du#One"/>
    </owl:disjointUnionOf>
  </owl:Class>
  <owl:Class rdf:about="http://example.org/du#Zero"/>
  <owl:Class rdf:about="http://example.org/du#One"/>
</rdf:RDF>""",
                "Prefix(ex:=<http://example.org/du#>) DisjointClasses(ex:Zero ex:One)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        # --- 2. Positive Entailment ---
        {
            "id": "PosEntail-001-RDFXML-SubClass",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe1",
                RDFXML_BIO,
                "Prefix(ex:=<http://example.org/bio#>) SubClassOf(ex:Dog ex:Animal)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-002-Turtle-ManagerEquiv",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe2",
                TURTLE_ORG,
                "Prefix(:=<http://example.org/org#>) ClassAssertion(:Manager :alice)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-003-FSS-SubObjectPropertyTransitive",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe3",
                """Prefix(:=<http://example.org/p#>)
Ontology(<http://example.org/p>
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  Declaration(ObjectProperty(:t))
  SubObjectPropertyOf(:r :s)
  SubObjectPropertyOf(:s :t)
)""",
                "SubObjectPropertyOf(:r :t)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-004-FSS-ObjectPropertyDomainInheritance",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe4",
                """Prefix(:=<http://example.org/dom#>)
Ontology(<http://example.org/dom>
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  SubClassOf(:A :B)
  SubObjectPropertyOf(:r :s)
  ObjectPropertyDomain(:s :A)
)""",
                "ObjectPropertyDomain(:r :B)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-005-FSS-FunctionalAndInverseProperty",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe5",
                """Prefix(:=<http://example.org/inv#>)
Ontology(<http://example.org/inv>
  Declaration(ObjectProperty(:p))
  Declaration(ObjectProperty(:q))
  InverseObjectProperties(:p :q)
  FunctionalObjectProperty(:p)
)""",
                "InverseFunctionalObjectProperty(:q)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-006-FSS-AnonIndividualExistentialQuery",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe6",
                """Prefix(:=<http://example.org/anon#>)
Ontology(<http://example.org/anon>
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(ObjectProperty(:r))
  Declaration(NamedIndividual(:a))
  ClassAssertion(ObjectSomeValuesFrom(:r :B) :a)
)""",
                "ClassAssertion(:B _:w)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-007-FSS-NaryDisjointClassesQuery",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe7",
                """Prefix(:=<http://example.org/nd#>)
Ontology(<http://example.org/nd>
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(Class(:C))
  DisjointClasses(:A :B :C)
)""",
                "DisjointClasses(:C :A :B)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-008-RDFXML-NegPropSymmetric",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe8",
                """<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:ex="http://example.org/sym#">
  <owl:Ontology rdf:about="http://example.org/sym"/>
  <owl:ObjectProperty rdf:about="http://example.org/sym#knows">
    <rdf:type rdf:resource="http://www.w3.org/2002/07/owl#SymmetricProperty"/>
  </owl:ObjectProperty>
  <owl:NamedIndividual rdf:about="http://example.org/sym#a"/>
  <owl:NamedIndividual rdf:about="http://example.org/sym#b"/>
  <owl:NegativePropertyAssertion>
    <owl:sourceIndividual rdf:resource="http://example.org/sym#a"/>
    <owl:assertionProperty rdf:resource="http://example.org/sym#knows"/>
    <owl:targetIndividual rdf:resource="http://example.org/sym#b"/>
  </owl:NegativePropertyAssertion>
</rdf:RDF>""",
                "Prefix(ex:=<http://example.org/sym#>) NegativeObjectPropertyAssertion(ex:knows ex:b ex:a)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-009-Turtle-OneOfNominalExhaustion",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe9",
                """@prefix : <http://example.org/nom#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
<http://example.org/nom> a owl:Ontology .
:Two a owl:Class ; owl:equivalentClass [ a owl:Class ; owl:oneOf ( :a :b ) ] .
:Good a owl:Class .
:a a owl:NamedIndividual , [ a owl:Class ; owl:complementOf :Good ] .
:b a owl:NamedIndividual .
:x a owl:NamedIndividual , :Two , :Good .
""",
                "Prefix(:=<http://example.org/nom#>) SameIndividual(:x :b)",
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
        {
            "id": "PosEntail-010-FSS-QualifiedCardinalityPigeonhole",
            "payload": [
                "sabrina-ofn-query-v1",
                "pe10",
                """Prefix(:=<http://example.org/qcr#>)
Ontology(<http://example.org/qcr>
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(ObjectProperty(:r))
  Declaration(NamedIndividual(:x))
  SubClassOf(:A ObjectMaxCardinality(1 :r :B))
  ClassAssertion(:A :x)
  ClassAssertion(ObjectMinCardinality(2 :r :B) :x)
)""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        # --- 3. Negative Entailment / Open-World Independence ---
        {
            "id": "NegEntail-001-RDFXML-OpenWorld",
            "payload": [
                "sabrina-ofn-query-v1",
                "ne1",
                RDFXML_BIO,
                "Prefix(ex:=<http://example.org/bio#>) ClassAssertion(ex:Dog ex:milo)",
            ],
            "expect_verdict": "SENTENCE_INDEPENDENT",
            "expect_verified": True,
        },
        {
            "id": "NegEntail-002-Turtle-NonSubsumption",
            "payload": [
                "sabrina-ofn-query-v1",
                "ne2",
                TURTLE_ORG,
                "Prefix(:=<http://example.org/org#>) SubClassOf(:Person :Employee)",
            ],
            "expect_verdict": "SENTENCE_INDEPENDENT",
            "expect_verified": True,
        },
        {
            "id": "NegEntail-003-FSS-SubPropNonEntailment",
            "payload": [
                "sabrina-ofn-query-v1",
                "ne3",
                """Prefix(:=<http://example.org/np#>)
Ontology(<http://example.org/np>
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  SubObjectPropertyOf(:r :s)
)""",
                "SubObjectPropertyOf(:s :r)",
            ],
            "expect_verdict": "SENTENCE_INDEPENDENT",
            "expect_verified": True,
        },
        # --- 4. W3C OWL 2 Datatype Map & Facets ---
        {
            "id": "Datatype-001-OwlRealOpenInterval",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt1",
                """Prefix(:=<http://example.org/dt#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/dt>
  Declaration(DataProperty(:p))
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(2 :p DatatypeRestriction(owl:real xsd:minExclusive "0"^^xsd:integer xsd:maxExclusive "1"^^xsd:integer)) :a)
)""",
            ],
            "expect_verdict": "SATISFIABLE",
            "expect_verified": True,
        },
        {
            "id": "Datatype-002-IntegerPigeonhole",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt2",
                """Prefix(:=<http://example.org/dt2#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/dt2>
  Declaration(DataProperty(:p))
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(3 :p DatatypeRestriction(xsd:integer xsd:minInclusive "1"^^xsd:integer xsd:maxInclusive "2"^^xsd:integer)) :a)
)""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Datatype-003-FloatZeroDistinctness",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt3",
                """Prefix(:=<http://example.org/dt3#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/dt3>
  Declaration(DataProperty(:p))
  Declaration(NamedIndividual(:a))
  FunctionalDataProperty(:p)
  DataPropertyAssertion(:p :a "-0.0"^^xsd:float)
  DataPropertyAssertion(:p :a "+0.0"^^xsd:float)
)""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        {
            "id": "Datatype-004-DateTimeStampTimelineFacet",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt4",
                """Prefix(:=<http://example.org/dt4#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/dt4>
  Declaration(DataProperty(:ts))
  Declaration(NamedIndividual(:e))
  DataPropertyRange(:ts DatatypeRestriction(xsd:dateTimeStamp xsd:minInclusive "2026-01-01T14:00:00+02:00"^^xsd:dateTimeStamp xsd:maxInclusive "2026-01-01T14:00:00+02:00"^^xsd:dateTimeStamp))
  DataPropertyAssertion(:ts :e "2026-01-01T12:00:00Z"^^xsd:dateTimeStamp)
)""",
            ],
            "expect_verdict": "SATISFIABLE",
            "expect_verified": True,
        },
        {
            "id": "Datatype-005-XSD11UnicodeRegexDigit",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt5",
                """Prefix(:=<http://example.org/dt5#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/dt5>
  Declaration(DataProperty(:code))
  Declaration(NamedIndividual(:a))
  DataPropertyRange(:code DatatypeRestriction(xsd:string xsd:pattern "\\\\d+"))
  DataPropertyAssertion(:code :a "\u0660\u0661"^^xsd:string)
)""",
            ],
            "expect_verdict": "SATISFIABLE",
            "expect_verified": True,
        },
        {
            "id": "Datatype-006a-XMLLiteralExcC14NCanonicalAccepted",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt6a",
                """Prefix(:=<http://example.org/dt6a#>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
Ontology(<http://example.org/dt6a>
  Declaration(DataProperty(:doc))
  Declaration(NamedIndividual(:a))
  DataPropertyAssertion(:doc :a "<a x=\\"1\\" y=\\"2\\"></a>"^^rdf:XMLLiteral)
)""",
            ],
            "expect_verdict": "SATISFIABLE",
            "expect_verified": True,
        },
        {
            "id": "Datatype-006b-XMLLiteralNonCanonicalRejected",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt6b",
                """Prefix(:=<http://example.org/dt6b#>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
Ontology(<http://example.org/dt6b>
  Declaration(DataProperty(:doc))
  Declaration(NamedIndividual(:a))
  DataPropertyAssertion(:doc :a "<a/>"^^rdf:XMLLiteral)
)""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        {
            "id": "Datatype-007-TurtleDatatypeRestrictionClash",
            "payload": [
                "sabrina-ofn-query-v1",
                "dt7",
                """@prefix : <http://example.org/dt7#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
<http://example.org/dt7> a owl:Ontology .
:age a owl:DatatypeProperty ;
  rdfs:range [
    a rdfs:Datatype ;
    owl:onDatatype xsd:integer ;
    owl:withRestrictions ( [ xsd:minInclusive 18 ] [ xsd:maxInclusive 65 ] )
  ] .
:kid a owl:NamedIndividual ; :age 12 .
""",
            ],
            "expect_verdict": "INCONSISTENT_ONTOLOGY",
            "expect_verified": True,
        },
        # --- 5. Strict W3C §5.8.2 & §11.2 Non-DL Rejection & Legal Punning ---
        {
            "id": "NonDL-001-NonSimpleRoleInCardinality",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl1",
                """Prefix(:=<http://example.org/ndl1#>)
Ontology(<http://example.org/ndl1>
  Declaration(Class(:A))
  Declaration(ObjectProperty(:r))
  TransitiveObjectProperty(:r)
  SubClassOf(:A ObjectMinCardinality(2 :r :A))
)""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        {
            "id": "NonDL-002-NonRegularRoleHierarchy",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl2",
                """Prefix(:=<http://example.org/ndl2#>)
Ontology(<http://example.org/ndl2>
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  SubObjectPropertyOf(ObjectPropertyChain(:r :s) :s)
  SubObjectPropertyOf(ObjectPropertyChain(:s :r) :r)
)""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        {
            "id": "NonDL-003-TopDataPropertySubProperty",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl3",
                """Prefix(:=<http://example.org/ndl3#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://example.org/ndl3>
  Declaration(DataProperty(:p))
  SubDataPropertyOf(owl:topDataProperty :p)
)""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        {
            "id": "NonDL-004-UndeclaredClassRejected",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl4",
                """Prefix(:=<http://example.org/ndl4#>)
Ontology(<http://example.org/ndl4>
  SubClassOf(:UndeclaredA :UndeclaredB)
)""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        {
            "id": "NonDL-005-IllegalObjDataPropertyPunning",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl5",
                """Prefix(:=<http://example.org/ndl5#>)
Ontology(<http://example.org/ndl5>
  Declaration(ObjectProperty(:p))
  Declaration(DataProperty(:p))
)""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        {
            "id": "NonDL-006-LegalClassIndividualPunningAccepted",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl6",
                """Prefix(:=<http://example.org/ndl6#>)
Ontology(<http://example.org/ndl6>
  Declaration(Class(:Species))
  Declaration(Class(:Eagle))
  Declaration(NamedIndividual(:Eagle))
  ClassAssertion(:Species :Eagle)
)""",
            ],
            "expect_verdict": "SATISFIABLE",
            "expect_verified": True,
        },
        {
            "id": "NonDL-007-MalformedRDFUnconsumedTriples",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl7",
                """@prefix : <http://example.org/bad#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
_:dangling rdf:first :A .
""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        {
            "id": "NonDL-008-AnonIndividualCycleRejected",
            "payload": [
                "sabrina-ofn-query-v1",
                "ndl8",
                """Prefix(:=<http://example.org/ndl8#>)
Ontology(<http://example.org/ndl8>
  Declaration(ObjectProperty(:r))
  ObjectPropertyAssertion(:r _:x _:y)
  ObjectPropertyAssertion(:r _:y _:x)
)""",
            ],
            "expect_verdict": "UNSUPPORTED",
            "expect_verified": False,
        },
        # --- 6. Cross-Syntax Multi-Document Import Closure ---
        {
            "id": "Import-001-RDFXMLImportingTurtle",
            "payload": [
                "sabrina-ofn-query-v1",
                "imp1",
                """<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:ex="http://example.org/base#">
  <owl:Ontology rdf:about="http://example.org/child">
    <owl:imports rdf:resource="http://example.org/base"/>
  </owl:Ontology>
  <owl:Class rdf:about="http://example.org/base#Sub">
    <rdfs:subClassOf rdf:resource="http://example.org/base#Mid"/>
  </owl:Class>
</rdf:RDF>""",
                "Prefix(ex:=<http://example.org/base#>) SubClassOf(ex:Sub ex:Top)",
                {
                    "http://example.org/base": """
@prefix : <http://example.org/base#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
<http://example.org/base> a owl:Ontology .
:Top a owl:Class .
:Mid a owl:Class ; rdfs:subClassOf :Top .
"""
                },
            ],
            "expect_verdict": "ENTAILED",
            "expect_verified": True,
        },
    ]


def run_classification_and_realization_tests() -> List[Tuple[str, bool, str]]:
    results: List[Tuple[str, bool, str]] = []

    # Classify-001 (Turtle)
    rc, res = run_query(["sabrina-classify-v1", "cls1", TURTLE_ORG], strict=True)
    cls = res.get("classification", {})
    unsat = cls.get("unsatisfiable", [])
    equivs = cls.get("equivalences", [])
    has_person_human = any(
        "http://example.org/org#Person" in grp and "http://example.org/org#Human" in grp
        for grp in equivs
    )
    ok = (
        rc == 0
        and res.get("verdict") == "CLASSIFIED"
        and res.get("lean_verified") is True
        and unsat == ["http://example.org/org#Ghost"]
        and has_person_human
    )
    results.append(("Classify-001-Turtle-HierarchyEquivUnsat", ok, json.dumps(res)[:200]))

    # Realize-001 (Turtle)
    rc, res = run_query(["sabrina-realize-v1", "rlz1", TURTLE_ORG], strict=True)
    entries = {e["individual"]: e for e in res.get("realization", {}).get("entries", [])}
    alice = entries.get("http://example.org/org#alice", {})
    ok = (
        rc == 0
        and res.get("verdict") == "REALIZED"
        and res.get("lean_verified") is True
        and "http://example.org/org#Manager" in alice.get("direct_types", [])
        and "http://example.org/org#Person" in alice.get("all_types", [])
        and "http://example.org/org#Person" not in alice.get("direct_types", [])
    )
    results.append(("Realize-001-Turtle-DirectAndAllTypes", ok, json.dumps(alice)))

    # Session-001 (RDF/XML loaded into persistent sabrina-session + classify + realize)
    cmds = [
        {"cmd": "load_tbox", "id": "bio-rdfxml", "ontology": RDFXML_BIO},
        {"cmd": "classify"},
        {"cmd": "realize"},
        {"cmd": "quit"},
    ]
    proc = subprocess.run(
        [str(SESSION_BIN)],
        input="\n".join(json.dumps(c) for c in cmds) + "\n",
        text=True,
        capture_output=True,
        timeout=30.0,
        check=True,
    )
    lines = [json.loads(l) for l in proc.stdout.strip().splitlines()]
    ok = (
        len(lines) == 4
        and lines[0].get("ok") is True
        and lines[1].get("cmd") == "classify"
        and lines[1].get("lean_verified") is True
        and lines[1].get("consistent") is True
        and lines[2].get("cmd") == "realize"
        and lines[2].get("lean_verified") is True
    )
    results.append(("Session-001-RDFXML-ClassifyAndRealize", ok, f"{len(lines)} responses"))
    return results


def main() -> int:
    if not QUERY_BIN.is_file() or not SESSION_BIN.is_file():
        print(f"ERROR: missing compiled binaries under {QUERY_BIN.parent}. Run 'lake build' first.", file=sys.stderr)
        return 1

    passed = 0
    failed: List[str] = []

    for case in build_cases():
        strict = case.get("strict", True)
        rc, res = run_query(case["payload"], strict=strict)
        verdict = res.get("verdict")
        verified = bool(res.get("lean_verified", False))
        ok = (
            res.get("format") == "sabrina-result-v1"
            and verdict == case["expect_verdict"]
            and verified == case["expect_verified"]
        )
        if ok:
            passed += 1
            print(f"  PASS  {case['id']} -> {verdict} (lean_verified={verified})")
        else:
            msg = (f"  FAIL  {case['id']}: got format={res.get('format')}, "
                   f"verdict={verdict}, verified={verified}, reason={res.get('reason')}")
            print(msg)
            failed.append(msg)

    for cid, ok, detail in run_classification_and_realization_tests():
        if ok:
            passed += 1
            print(f"  PASS  {cid}")
        else:
            msg = f"  FAIL  {cid}: {detail}"
            print(msg)
            failed.append(msg)

    total = passed + len(failed)
    print(f"\nW3C OWL 2 DL Conformance Gate: {passed}/{total} passed.")
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
