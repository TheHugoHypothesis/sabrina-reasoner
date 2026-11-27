import Sabrina.CLI.Response
import Sabrina.CLI.DataQuery
import Sabrina.CLI.SROIQDQuery
import Sabrina.CLI.OFNQuery
import Sabrina.CLI.ImportCatalog

namespace Sabrina.CLI.Query

open Lean
open Sabrina.CLI (response)

private def solveJSON (j : Json) (cliStrict : Bool := false)
    (extraLib : List (Sabrina.OWL2.IRI × String) := []) : UInt32 × Json :=
  let version : Option Json := j.getArr?.toOption.bind fun fields => fields[0]?
  match version with
  | some (.str format) =>
    if format == DataQuery.requestFormat then DataQuery.run j
    else if format == SROIQDQuery.requestFormat then SROIQDQuery.run j
    else if format == OFNQuery.requestFormat then OFNQuery.run j cliStrict extraLib
    else if format == OFNQuery.classifyFormat then OFNQuery.runClassify j cliStrict extraLib
    else if format == OFNQuery.realizeFormat then OFNQuery.runRealize j cliStrict extraLib
    else if format == OFNQuery.materializeFormat then OFNQuery.runMaterialize j cliStrict extraLib
    else if format == OFNQuery.explainFormat then OFNQuery.runExplain j cliStrict extraLib
    else (2, response "UNSUPPORTED" false [("reason", toJson s!"unsupported request format: {format}")])
  | _ => (2, response "UNSUPPORTED" false [("reason", toJson "expected a JSON array starting with a request format")])

private structure CliConfig where
  strictOwl2DL : Bool := false
  extraLib : List (Sabrina.OWL2.IRI × String) := []
  classifyInput : Option String := none
  summaryOnly : Bool := false
  workers : Nat := 8
  materializeInput : Option String := none
  explainInput : Option String := none
  explainQuery : Option String := none
  maxJustifications : Nat := 5
  outputPath : Option String := none
  outputFormat : Option Sabrina.OWL2.Materialize.OutputFormat := none
  matOpts : Sabrina.OWL2.Materialize.MaterializeOptions := {}

private def parseCliArgs (args : List String) : IO (Except String CliConfig) := do
  let mut cfg : CliConfig := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--strict-owl2dl" :: tail =>
      cfg := { cfg with strictOwl2DL := true }
      rest := tail
    | "--catalog" :: path :: tail =>
      match ← ImportCatalog.loadOasisCatalog (System.FilePath.mk path) with
      | .ok lib => cfg := { cfg with extraLib := cfg.extraLib ++ lib }
      | .error err => return .error err
      rest := tail
    | "--import-dir" :: dir :: tail =>
      match ← ImportCatalog.loadImportDir (System.FilePath.mk dir) with
      | .ok lib => cfg := { cfg with extraLib := cfg.extraLib ++ lib }
      | .error err => return .error err
      rest := tail
    | "--classify" :: path :: tail =>
      cfg := { cfg with classifyInput := some path }
      rest := tail
    | "--summary-only" :: tail =>
      cfg := { cfg with summaryOnly := true }
      rest := tail
    | "--workers" :: nStr :: tail =>
      match nStr.toNat? with
      | some n => cfg := { cfg with workers := max 1 n }
      | none => return .error s!"expected natural number for --workers, got '{nStr}'"
      rest := tail
    | "--materialize" :: path :: tail =>
      cfg := { cfg with materializeInput := some path }
      rest := tail
    | "--explain" :: path :: tail =>
      cfg := { cfg with explainInput := some path }
      rest := tail
    | "--query" :: qText :: tail =>
      cfg := { cfg with explainQuery := some qText }
      rest := tail
    | "--max-justifications" :: nStr :: tail =>
      match nStr.toNat? with
      | some n => cfg := { cfg with maxJustifications := n }
      | none => return .error s!"expected natural number for --max-justifications, got '{nStr}'"
      rest := tail
    | "-o" :: path :: tail | "--output" :: path :: tail =>
      cfg := { cfg with outputPath := some path }
      rest := tail
    | "--format" :: fmtStr :: tail =>
      match Sabrina.OWL2.Materialize.OutputFormat.ofString? fmtStr with
      | some f => cfg := { cfg with outputFormat := some f }
      | none => return .error s!"unsupported --format '{fmtStr}' (expected: ofn, ttl, rdfxml)"
      rest := tail
    | "--inferred-only" :: tail =>
      cfg := { cfg with matOpts := { cfg.matOpts with includeAsserted := false } }
      rest := tail
    | "--all-inferred" :: tail =>
      cfg := { cfg with matOpts := { cfg.matOpts with includeAllSubClass := true, includeAllTypes := true } }
      rest := tail
    | flag :: _ =>
      return .error s!"unknown or incomplete CLI flag: {flag} (supported: --strict-owl2dl, --catalog <path>, --import-dir <dir>, --classify <in>, --summary-only, --workers <n>, --materialize <in>, --explain <in>, --query <ofn>, --max-justifications <n>, -o <out>, --format <ofn|ttl|rdfxml>, --inferred-only, --all-inferred)"
    | [] => break
  return .ok cfg

def run (args : List String) : IO UInt32 := do
  let cfg ← match ← parseCliArgs args with
    | .ok res => pure res
    | .error err =>
      IO.println (response "UNSUPPORTED" false [("reason", toJson err)]).compress
      return 2
  if let some inPath := cfg.classifyInput then
    let docText ← try
        IO.FS.readFile (System.FilePath.mk inPath)
      catch e =>
        IO.println (response "UNSUPPORTED" false [("reason", toJson s!"failed to read '{inPath}': {e}")]).compress
        return 2
    let (code, outJson) := OFNQuery.runClassifyDocument inPath docText
      cfg.extraLib cfg.strictOwl2DL cfg.workers cfg.summaryOnly
    IO.println outJson.compress
    return code
  if let some inPath := cfg.explainInput then
    let docText ← try
        IO.FS.readFile (System.FilePath.mk inPath)
      catch e =>
        IO.println (response "UNSUPPORTED" false [("reason", toJson s!"failed to read '{inPath}': {e}")]).compress
        return 2
    let (code, outJson) := OFNQuery.runExplainDocument inPath docText cfg.explainQuery
      cfg.extraLib cfg.strictOwl2DL cfg.maxJustifications
    IO.println outJson.compress
    return code
  if let some inPath := cfg.materializeInput then
    let docText ← try
        IO.FS.readFile (System.FilePath.mk inPath)
      catch e =>
        IO.println (response "UNSUPPORTED" false [("reason", toJson s!"failed to read '{inPath}': {e}")]).compress
        return 2
    let fmt := match cfg.outputFormat, cfg.outputPath with
      | some f, _ => f
      | none, some outP => Sabrina.OWL2.Materialize.OutputFormat.fromPath outP
      | none, none => Sabrina.OWL2.Materialize.OutputFormat.fromPath inPath
    let (code, metaJson, rendered?) :=
      OFNQuery.runMaterializeDocument inPath docText cfg.extraLib cfg.strictOwl2DL fmt cfg.matOpts
    match rendered?, cfg.outputPath with
    | some txt, some outP =>
      try
        IO.FS.writeFile (System.FilePath.mk outP) txt
      catch e =>
        IO.println (response "UNSUPPORTED" false [("reason", toJson s!"failed to write '{outP}': {e}")]).compress
        return 2
      let outJson := match metaJson.getObj? with
        | .ok obj => Json.mkObj (("output_path", toJson outP) :: obj.toList)
        | .error _ => metaJson
      IO.println outJson.compress
      return code
    | some txt, none =>
      IO.print txt
      return code
    | none, _ =>
      IO.println metaJson.compress
      return code
  let input ← (← IO.getStdin).readToEnd
  let (code, result) := match Json.parse input with
    | .ok j => solveJSON j cfg.strictOwl2DL cfg.extraLib
    | .error reason => (2, response "UNSUPPORTED" false [("reason", toJson reason)])
  IO.println result.compress
  return code

end Sabrina.CLI.Query
