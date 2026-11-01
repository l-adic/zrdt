/-
A local stand-in for `lake comparator` (docs/PLAN.md §5), for machines where its `bwrap` sandbox
cannot run. It is NOT the comparator verdict: it loads the project's own `.olean` files into its
own process, which the sandbox exists to avoid. Run it with

    lake build Crdt.Merkle.Api Comparator.Challenge
    lake env lean --run scripts/CompareStatements.lean

It reads the names and permitted axioms from `comparator.json`, and for each name checks that
the solution (`solution_module`) declares a theorem whose statement and universe parameters are
exactly those of the challenge (`challenge_module`), and whose axioms are all permitted. The
kernel replay is `leanchecker` (see `make comparator-local`).
-/
import Lean
open Lean

def strs (j : Json) (k : String) : Except String (Array String) := do
  let a ← (← j.getObjVal? k).getArr?
  a.mapM (·.getStr?)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "comparator.json"))
  let chal := (← IO.ofExcept (j.getObjValAs? String "challenge_module")).toName
  let sol := (← IO.ofExcept (j.getObjValAs? String "solution_module")).toName
  let names := (← IO.ofExcept (strs j "theorem_names")).map String.toName
  let permitted := (← IO.ofExcept (strs j "permitted_axioms")).map String.toName
  let ce ← importModules #[{ module := chal }] {}
  let se ← importModules #[{ module := sol }] {}
  let mut bad := 0
  for n in names do
    match ce.find? n, se.find? n with
    | some c, some s@(.thmInfo _) =>
      if c.type != s.type || c.levelParams != s.levelParams then
        IO.println s!"MISMATCH {n}: the statements differ"; bad := bad + 1
      else
        let (axs, _) ← (collectAxioms n : CoreM _).toIO { fileName := "", fileMap := default }
          { env := se }
        let extra := axs.filter (!permitted.contains ·)
        if extra.isEmpty then IO.println s!"ok       {n}  {axs.toList}"
        else IO.println s!"AXIOMS   {n}: not permitted {extra.toList}"; bad := bad + 1
    | none, _ => IO.println s!"MISSING  {n} in the challenge"; bad := bad + 1
    | _, some _ => IO.println s!"NOT A THEOREM {n} in the solution"; bad := bad + 1
    | _, none => IO.println s!"MISSING  {n} in the solution"; bad := bad + 1
  if bad == 0 then
    IO.println s!"statements match: {names.size} theorems, axioms within {permitted.toList}"
    return 0
  else
    IO.println s!"{bad} problem(s)"
    return 1
