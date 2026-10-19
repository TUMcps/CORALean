module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet

@[expose] public section

/-!
# `PolyLevelSet.and_` over a floating-point scalar

`Real.PolyLevelSet.and_` at the stored floats: the rows of both operands stacked over shared
variables, each over its own monomials, the off-blocks `zero` and every entry and slack copied, so
nothing rounds (`eval_nominalCore_and_`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both constraint systems, each with its own operators and slacks, over both monomial lists, on
the boxes' intersection. -/
def PolyLevelSet.and_ (P₁ P₂ : PolyLevelSet 𝕋 n) : PolyLevelSet 𝕋 n where
  m := P₁.m + P₂.m
  q := P₁.q + P₂.q
  A := Fin.append (fun i => Fin.append (P₁.A i) fun _ => zero)
    (fun i => Fin.append (fun _ => zero) (P₂.A i))
  R k := Fin.append (P₁.R k) (P₂.R k)
  b := Fin.append P₁.b P₂.b
  b_error := Fin.append P₁.b_error P₂.b_error
  op := Fin.append P₁.op P₂.op
  dom := P₁.dom.intersection P₂.dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
