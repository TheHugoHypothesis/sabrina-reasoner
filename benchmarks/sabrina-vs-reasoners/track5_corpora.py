"""Prepare and verify the exact OFN inputs used in the published Track 5 results."""

from __future__ import annotations

import gzip
import hashlib
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

BENCH_DIR = Path(__file__).resolve().parent
CORP_DIR = BENCH_DIR / "corpora"


@dataclass(frozen=True)
class Corpus:
    slug: str
    label: str
    source_url: str
    owl_sha256: str | None
    ofn_sha256: str

    @property
    def ofn_path(self) -> Path:
        return CORP_DIR / f"{self.slug}.ofn"


CORPORA = (
    Corpus(
        "cl-basic",
        "CL-basic (Cell Ontology)",
        "https://purl.obolibrary.org/obo/cl/releases/2026-11-13/cl-basic.owl",
        "963f7d9e0e1d78e586abf8eb185d85a3ef8529743589ea651ea0796001c37d61",
        "9c0b532d5e3edd25275e42454e76e477b4b80850c6bf38c041526ddcdaeb94f2",
    ),
    Corpus(
        "doid",
        "DOID (Human Disease)",
        "https://purl.obolibrary.org/obo/doid/releases/2026-10-29/doid.owl",
        "f766045282299e53dc369ebf5600436b11a9b6ed1dcd3af5cc9b7b5d6b452600",
        "13691a31285584799ac09b36fef69b6422ffa7bd0de404f4ce5e03e48d241ee2",
    ),
    Corpus(
        "uberon-basic",
        "UBERON-basic (Anatomy)",
        "https://purl.obolibrary.org/obo/uberon/releases/2026-11-05/uberon-basic.owl",
        "7f14744077f8daf08c6f610eaf430e6cc429b53cf196065ab3d5948c0737df4c",
        "64fc95bc6222f679adcf93dedcff3145759eee726d214f49b34e58e51f8f0d81",
    ),
    Corpus(
        "go-basic",
        "GO-basic (Gene Ontology)",
        "https://current.geneontology.org/ontology/go-basic.owl",
        None,
        "515571fdab6fecd93b02d14e758729fb172d7965ab6043a59f592abc2d5d8d0f",
    ),
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_sha256(path: Path, expected: str) -> None:
    actual = sha256_file(path)
    if actual != expected:
        raise ValueError(f"SHA-256 mismatch for {path}: expected {expected}, got {actual}")


def converter_classpath() -> str:
    harness = BENCH_DIR / "java-harness"
    classes = harness / "target" / "classes"
    dependencies = harness / "target" / "classpath.txt"
    if not dependencies.is_file() or not (classes / "bench" / "ConvertToOfn.class").is_file():
        subprocess.run(
            ["mvn", "-q", "compile", "dependency:build-classpath", "-Dmdep.outputFile=target/classpath.txt"],
            cwd=harness,
            check=True,
        )
    return f"{classes}:{dependencies.read_text(encoding='utf-8').strip()}"


def main() -> None:
    CORP_DIR.mkdir(exist_ok=True)
    classpath = None
    for corpus in CORPORA:
        destination = corpus.ofn_path
        if destination.is_file() and sha256_file(destination) == corpus.ofn_sha256:
            print(f"Verified cached input {destination}", flush=True)
            continue
        with TemporaryDirectory(dir=CORP_DIR) as scratch:
            output = Path(scratch) / destination.name
            if corpus.owl_sha256 is None:
                snapshot = BENCH_DIR / "snapshots" / f"{corpus.slug}.ofn.gz"
                with gzip.open(snapshot, "rb") as compressed, output.open("wb") as ofn:
                    shutil.copyfileobj(compressed, ofn)
            else:
                if classpath is None:
                    classpath = converter_classpath()
                owl = output.with_suffix(".owl")
                print(f"Downloading {corpus.slug} from {corpus.source_url}", flush=True)
                subprocess.run(
                    ["curl", "-fsSL", "--retry", "2", "--max-time", "90", "-o", str(owl), corpus.source_url],
                    check=True,
                )
                verify_sha256(owl, corpus.owl_sha256)
                subprocess.run(
                    ["java", "--add-opens", "java.base/java.lang=ALL-UNNAMED", "-Xmx4g",
                     "-cp", classpath, "bench.ConvertToOfn", str(owl), str(output)],
                    check=True,
                )
            verify_sha256(output, corpus.ofn_sha256)
            output.replace(destination)
            print(f"Prepared verified input {destination}", flush=True)


if __name__ == "__main__":
    main()
