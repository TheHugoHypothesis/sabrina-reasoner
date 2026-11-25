#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR=""

usage() {
  cat <<EOF
Usage: $0 --out-dir <external-output-dir>

Runs the standalone SABRINA reproducible benchmarks and writes raw JSON logs
(Track 5 OBO Foundry, Track 6 Exact OWL 2 DL, and Cross-Reasoner Boundary Audit)
into <external-output-dir>/raw/.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage; exit 2 ;;
  esac
done

if [[ -z "$OUT_DIR" ]]; then
  echo "ERROR: --out-dir is required." >&2
  usage
  exit 2
fi

mkdir -p "$OUT_DIR/raw"
OUT_DIR_ABS="$(cd "$OUT_DIR" && pwd)"

if [[ ! -f "$SCRIPT_DIR/java-harness/target/classpath.txt" ]]; then
  echo "[0/3] Building Java OWL API 5 harness (HermiT 1.4.5 + ELK 0.6.0)..."
  (cd "$SCRIPT_DIR/java-harness" && mvn -q compile dependency:build-classpath -Dmdep.outputFile=target/classpath.txt)
fi

echo "[1/3] Ensuring OBO Foundry corpora & executing Track 5 (CL, DOID, UBERON, GO-basic up to 71,501 axioms)..."
"$SCRIPT_DIR/download_corpora.sh"
python3 "$SCRIPT_DIR/run_track5_obo.py" --out-dir "$OUT_DIR_ABS"

echo "[2/3] Executing Track 6 (15 W3C OWL 2 DL conformant queries + 3 non-DL §11.2 extensions)..."
python3 "$SCRIPT_DIR/run_track6_exact_owl2dl.py" --out-dir "$OUT_DIR_ABS"

echo "[3/3] Executing Cross-Reasoner Role-Hierarchy Boundary Audit (T1-T5)..."
python3 "$SCRIPT_DIR/run_boundary_audit.py" --out "$OUT_DIR_ABS/raw/boundary_reasoner_audit.json"

echo "Done! Raw JSON logs written to: $OUT_DIR_ABS/raw/"
ls -la "$OUT_DIR_ABS/raw/"
