module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `PolyLevelSet.cartProd` over a floating-point scalar

`Real.PolyLevelSet.cartProd` at the stored floats: the rows of both operands stacked, each over
its own variables, the off-blocks `zero` and every entry and slack copied, so nothing rounds
(`eval_nominalCore_cartProd`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both constraint systems, each on its own block of variables and box, each row with its own
slack. -/
def PolyLevelSet.cartProd (P₁ : PolyLevelSet 𝕋 n₁) (P₂ : PolyLevelSet 𝕋 n₂) :
    PolyLevelSet 𝕋 (n₁ + n₂) where
  m := P₁.m + P₂.m
  q := P₁.q + P₂.q
  A := Fin.append (fun i => Fin.append (P₁.A i) fun _ => zero)
    (fun i => Fin.append (fun _ => zero) (P₂.A i))
  R := Real.PolyZonotope.plusE P₁.R P₂.R
  b := Fin.append P₁.b P₂.b
  b_error := Fin.append P₁.b_error P₂.b_error
  op := Fin.append P₁.op P₂.op
  dom := P₁.dom.append P₂.dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
