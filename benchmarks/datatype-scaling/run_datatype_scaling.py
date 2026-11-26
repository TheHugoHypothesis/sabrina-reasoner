#!/usr/bin/env python3
"""Regression benchmark for RDF ontology-header annotations, import-closure
declaration sharing, and multi-datatype SROIQ(D) preparation & classification.

Runs `sabrina-query --classify` on synthetic Turtle inputs covering undeclared
header metadata (`xsd:date`), cross-file `owl:AnnotationProperty` declarations,
and 28 distinct OWL 2 datatype families under non-EL SROIQ(D).
"""
import os, subprocess, sys, tempfile, time, resource

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.path.join(ROOT, ".lake/build/bin/sabrina-query")
TIMEOUT = float(os.environ.get("DATATYPE_SCALING_TIMEOUT", "30"))

PFX = """@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix dcterms: <http://purl.org/dc/terms/> .
@prefix ex: <http://example.org/ont#> .
"""
DTS = ["xsd:string", "xsd:normalizedString", "xsd:token", "xsd:Name", "xsd:NCName",
       "xsd:integer", "xsd:int", "xsd:long", "xsd:short", "xsd:byte",
       "xsd:nonNegativeInteger", "xsd:positiveInteger", "xsd:unsignedInt",
       "xsd:decimal", "owl:real", "owl:rational", "xsd:double", "xsd:float",
       "xsd:boolean", "xsd:dateTime", "xsd:dateTimeStamp", "xsd:anyURI",
       "xsd:hexBinary", "xsd:base64Binary", "rdf:XMLLiteral", "rdf:PlainLiteral",
       "xsd:nonPositiveInteger", "xsd:negativeInteger"]

def datatype_ontology(n_some):
    L = [PFX, '<http://example.org/ont> a owl:Ontology ; dcterms:modified "2026-11-17"^^xsd:date .']
    for i, dt in enumerate(DTS):
        L.append(f"ex:dp{i} a owl:DatatypeProperty ; rdfs:range {dt} .")
        L.append(f"ex:C{i} a owl:Class ; rdfs:subClassOf [ a owl:Restriction ; owl:onProperty ex:dp{i} ; owl:allValuesFrom {dt} ] .")
    L += ["ex:hasPart a owl:ObjectProperty .",
          "ex:partOf a owl:ObjectProperty ; owl:inverseOf ex:hasPart .",
          "ex:System a owl:Class ; rdfs:subClassOf [ a owl:Class ; owl:unionOf ( ex:C0 ex:C1 ) ] .",
          "ex:s1 a ex:System ."]
    for i in range(n_some):
        L.append(f"ex:System rdfs:subClassOf [ a owl:Restriction ; owl:onProperty ex:dp{i} ; owl:someValuesFrom {DTS[i]} ] .")
    return "\n".join(L) + "\n"

CASES = {
    "named-header-date": PFX + """<http://example.org/ont> a owl:Ontology ;
  dcterms:modified "2026-11-17"^^xsd:date ; ex:customHeaderDate "2024-06-15"^^xsd:date .
ex:Device a owl:Class . ex:Sensor a owl:Class ; rdfs:subClassOf ex:Device ;
  dcterms:modified "2026-11-18"^^xsd:date .
""",
    "bnode-header-date": PFX + """[] a owl:Ontology ; ex:releasedOn "2026-11-17"^^xsd:date .
ex:A a owl:Class .
""",
    "28-atoms-allValuesFrom": datatype_ontology(0),
    "28-atoms-15-someValuesFrom": datatype_ontology(15),
    "28-atoms-28-someValuesFrom": datatype_ontology(28),
}

def run(path, extra=()):
    t0 = time.perf_counter()
    p = subprocess.Popen([BIN, *extra, "--classify", path, "--summary-only"],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        out, _ = p.communicate(timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        p.kill(); p.communicate()
        return None, TIMEOUT, ""
    return p.returncode, time.perf_counter() - t0, out

def main():
    ok = True
    with tempfile.TemporaryDirectory() as d:
        for name, ttl in CASES.items():
            f = os.path.join(d, name + ".ttl"); open(f, "w").write(ttl)
            rc, dt, out = run(f)
            good = rc == 0 and '"consistent":true' in out and '"lean_verified":true' in out
            ok &= good
            print(f"{'PASS' if good else 'FAIL'}  {name:30s} rc={rc} {dt:6.2f}s  {out.strip()[:140]}")
        # Cross-file: annotation property declared only in the imported document
        sub = os.path.join(d, "imports"); os.mkdir(sub)
        open(os.path.join(sub, "vocab.ttl"), "w").write(PFX +
            "<http://example.org/vocab> a owl:Ontology .\nex:myCustomDate a owl:AnnotationProperty .\n")
        root = os.path.join(d, "root.ttl")
        open(root, "w").write(PFX + """<http://example.org/root> a owl:Ontology ; owl:imports <http://example.org/vocab> .
ex:Component a owl:Class ; ex:myCustomDate "2026-11-17"^^xsd:date .
""")
        rc, dt, out = run(root, ("--import-dir", sub))
        good = rc == 0 and '"consistent":true' in out
        ok &= good
        print(f"{'PASS' if good else 'FAIL'}  {'cross-file-annotation-decl':30s} rc={rc} {dt:6.2f}s")
    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024
    print(f"peak child RSS: {peak:.1f} MiB")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
