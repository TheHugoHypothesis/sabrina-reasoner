#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR=""

usage() {
  cat <<EOF
Usage: $0 --out-dir <external-output-dir>

Runs all six SABRINA benchmark tracks and the role hierarchy boundary audit.
Writes raw JSON logs into <external-output-dir>/raw/.
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
  echo "Building the Java harness (HermiT 1.4.5 and ELK 0.6.0)..."
  (cd "$SCRIPT_DIR/java-harness" && mvn -q compile dependency:build-classpath -Dmdep.outputFile=target/classpath.txt)
fi

echo "[1/4] Running Tracks 1 through 4..."
python3 "$SCRIPT_DIR/run_eval.py" --out-dir "$OUT_DIR_ABS"

echo "[2/4] Preparing pinned OBO Foundry corpora and running Track 5..."
"$SCRIPT_DIR/download_corpora.sh"
python3 "$SCRIPT_DIR/run_track5_obo.py" --out-dir "$OUT_DIR_ABS"

echo "[3/4] Running Track 6..."
python3 "$SCRIPT_DIR/run_track6_exact_owl2dl.py" --out-dir "$OUT_DIR_ABS"

echo "[4/4] Running the cross-reasoner role hierarchy audit..."
python3 "$SCRIPT_DIR/run_boundary_audit.py" --out "$OUT_DIR_ABS/raw/boundary_reasoner_audit.json"

echo "Done! Raw JSON logs written to: $OUT_DIR_ABS/raw/"
ls -la "$OUT_DIR_ABS/raw/"
