import Zrdt.Vectors

/-!
# Print `vectors/vectors.json` (`make vectors`)

The vectors and their checks live in `Zrdt.Vectors`, which the library imports, so a plain
`lake build` runs the checks. This file only prints them. It is run with `lake env lean --run`
and is in no library, so its `main` never meets `zrdtd`'s.

The build text in the file is the one `zrdtd` reports when it is built from the same sources: it
covers `Zrdtd/Main.lean` too (`Proto.buildIdOf`). This file reads `Main.lean` itself, each time it
runs.
-/

/-- Print `vectors/vectors.json`, or name the steps that do not give their expected reply. -/
def main : IO UInt32 := do
  match Zrdt.Vectors.failures with
  | [] =>
    let build := Zrdt.Proto.buildIdOf (include_str "Main.lean")
    IO.println ((Zrdt.Vectors.vectors build).render "")
    return 0
  | bad =>
    IO.eprintln s!"vectors: these steps do not give their expected reply: {bad}"
    return 1
