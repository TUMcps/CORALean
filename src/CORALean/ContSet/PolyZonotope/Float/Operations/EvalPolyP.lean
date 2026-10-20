module

public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyStep

@[expose] public section

/-!
# `evalPoly`'s recursion, over a floating-point scalar

Not merged into `EvalPoly.lean`: the recursion cannot be written without its proof. Every
`evalPolyStep` needs `hp : R.p = pZ.p` for the accumulated `R`, so the recursion returns the set
together with that proof. `evalPoly` is its first projection, `evalPoly_p` its second, and
`Theorems/EvalPolyOuter.lean` unfolds the recursion itself, so it has users outside `evalPoly`.

## Inputs
* `pZ` – polynomial zonotope

## Output
* evaluator mapping coefficients to a set with the same factor count
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `evalPoly`'s recursion, paired with the proof that it never leaves `pZ`'s
factor count. -/
def PolyZonotope.evalPolyP (pZ : PolyZonotope (Vec 𝕋 n)) :
    List (Vec 𝕋 n) → {R : PolyZonotope (Vec 𝕋 n) // R.p = pZ.p}
  | [] => ⟨(⟨pZ.p, 0, 0, fun _ => zero, Fin.elim0, fun _ => Fin.elim0, Fin.elim0,
      ⟨fun _ => zero, fun _ => zero⟩⟩ : PolyZonotope (Vec 𝕋 n)), rfl⟩
  | a :: rest =>
      let R := PolyZonotope.evalPolyP pZ rest
      ⟨PolyZonotope.evalPolyStep R.1 pZ R.2 a, R.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
