#!/usr/bin/env python3
"""Exercise compiled evaluation of valid and invalid certificate trees."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
program = r'''
import LogicTests.CertificateExamples
open Logic.FOL Logic.Proof
def q (n : Nat) : Formula String String Nat := .rel "p" [.var n]
#eval check [] (.impl (q 0) (q 0)) identityCertificate
#eval check [] (.impl (q 0) (q 1)) identityCertificate
#eval check [.allv 0 (q 0)] (.allv 0 (q 0)) quantifiedCertificate
#eval check [q 1] (.allv 0 (q 0)) (.allIntro 1 .assumption)
#eval check [.exv 0 (q 0)] (.exv 0 (q 0)) identityExistentialCertificate
#eval check [] (.eql (.var 0) (.var 1) : Formula String String Nat) .eqRefl
'''
proc = subprocess.run(["lake", "env", "lean", "--stdin"], input=program,
                      text=True, capture_output=True, cwd=root, check=True)
expected = ["true", "false", "true", "false", "true", "false"]
actual = proc.stdout.splitlines()
if actual != expected:
    raise AssertionError(f"unexpected checker output: {actual!r}; stderr={proc.stderr!r}")
print("certificate runtime regression cases passed")
