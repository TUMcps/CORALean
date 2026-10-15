module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyStep

@[expose] public section

/-!
# `evalPoly`'s recursion, paired with its factor-count proof

Not merged into `EvalPoly.lean`: every `mul` step needs the factor-count proof of the previous
step, so the recursion returns the set together with that proof, and `evalPoly` is its first
projection. It has users of its own: the float layer's `evalPoly`, `EvalPolySortP`, `PowSort`,
`Theorems/EvalPolyOuter.lean` and `Theorems/EvalPolyExact.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `evalPoly`'s recursion, paired with the proof that it never leaves `pZ`'s
factor count — carried along so the next step's `mul` needs no new one. -/
def PolyZonotope.evalPolyP (pZ : PolyZonotope (Vec ℝ n)) :
    List (Vec ℝ n) → {R : PolyZonotope (Vec ℝ n) // R.p = pZ.p}
  | [] =>
      ⟨(⟨pZ.p, 0, 0, 0, Fin.elim0, fun _ => Fin.elim0, Fin.elim0⟩ : PolyZonotope (Vec ℝ n)), rfl⟩
  | a :: rest =>
      let R := PolyZonotope.evalPolyP pZ rest
      ⟨PolyZonotope.evalPolyStep R.1 pZ R.2 a, R.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
