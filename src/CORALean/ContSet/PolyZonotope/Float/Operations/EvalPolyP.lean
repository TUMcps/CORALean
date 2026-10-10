import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyStep

/-!
# `evalPoly`'s recursion, over a floating-point scalar

Split out of `EvalPoly.lean` (issue #62): read again by
`Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `evalPoly`'s recursion, paired with the proof that it never leaves `pZ`'s
factor count. -/
def PolyZonotope.evalPolyP (pZ : PolyZonotope 𝕋 n) :
    List (Vec 𝕋 n) → {R : PolyZonotope 𝕋 n // R.p = pZ.p}
  | [] => ⟨(⟨pZ.p, 0, 0, fun _ => zero, Fin.elim0, fun _ => Fin.elim0, Fin.elim0,
      ⟨fun _ => zero, fun _ => zero⟩⟩ : PolyZonotope 𝕋 n), rfl⟩
  | a :: rest =>
      let R := PolyZonotope.evalPolyP pZ rest
      ⟨PolyZonotope.evalPolyStep R.1 pZ R.2 a, R.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
