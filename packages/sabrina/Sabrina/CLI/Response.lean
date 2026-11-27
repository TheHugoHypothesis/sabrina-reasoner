import Lean.Data.Json

namespace Sabrina.CLI

open Lean

/-- The JSON envelope shared by document and typed query results. -/
def response (verdict : String) (verified : Bool) (fields : List (String × Json)) : Json :=
  Json.mkObj ([
    ("format", toJson "sabrina-result-v1"),
    ("verdict", toJson verdict),
    ("lean_verified", toJson verified)
  ] ++ fields)

end Sabrina.CLI
