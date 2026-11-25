#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CORP="$SCRIPT_DIR/corpora"
mkdir -p "$CORP"

if [[ ! -f "$SCRIPT_DIR/java-harness/target/classpath.txt" ]]; then
  (cd "$SCRIPT_DIR/java-harness" && mvn -q compile dependency:build-classpath -Dmdep.outputFile=target/classpath.txt)
fi
CP="$SCRIPT_DIR/java-harness/target/classes:$(cat "$SCRIPT_DIR/java-harness/target/classpath.txt")"

download_and_convert() {
  local name="$1"
  local url="$2"
  if [[ ! -f "$CORP/$name.ofn" ]]; then
    echo "Downloading $name from $url..."
    curl -sSL --max-time 90 "$url" -o "$CORP/$name.owl"
    java --add-opens java.base/java.lang=ALL-UNNAMED -Xmx4g -cp "$CP" \
      bench.ConvertToOfn "$CORP/$name.owl" "$CORP/$name.ofn" 2>/dev/null
  else
    echo "Cached: $CORP/$name.ofn"
  fi
}

download_and_convert "cl-basic"     "http://purl.obolibrary.org/obo/cl/cl-basic.owl"
download_and_convert "doid"         "http://purl.obolibrary.org/obo/doid.owl"
download_and_convert "uberon-basic" "http://purl.obolibrary.org/obo/uberon/uberon-basic.owl"
download_and_convert "go-basic"     "http://purl.obolibrary.org/obo/go/go-basic.owl"
