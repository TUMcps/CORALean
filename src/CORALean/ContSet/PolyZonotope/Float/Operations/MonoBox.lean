module

public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.Power
public import CORALean.ContSet.Interval.Float.Operations.Prod1

@[expose] public section

/-!
# `PolyZonotope.monoBox`

The interval evaluation of the monomials `∏ₖ αₖ^{E[k,l]}` over a box of factor values, as
CORA's `prod(x.^E(:,i),1)` evaluates them on an interval `x` in `aux_funcPoly` and in the
Jacobian handle of `@polyZonotope/contains_`: each power by `Interval.power`, which keeps an
even power of an interval around `0` nonnegative, and the product over the factors by
`Interval.prod₁`, every corner rounded outward, and stored (`materialise`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An interval for each monomial of the exponent matrix `E` over the factor box `X`. -/
def PolyZonotope.monoBox {p h : ℕ} (E : Fin p → Fin h → ℕ) (X : Interval (Vec 𝕋 p)) :
    Interval (Vec 𝕋 h) :=
  -- the factor `k` alone, as a box of one coordinate
  let Xk : Fin p → Interval (Vec 𝕋 1) := fun k => ⟨fun _ => X.inf k, fun _ => X.sup k⟩
  -- entry `(k, l)`: `x_k .^ E(k, l)`
  let P : Interval (Mat 𝕋 p h) :=
    ⟨fun k l => ((Xk k).power (E k l)).inf 0, fun k l => ((Xk k).power (E k l)).sup 0⟩
  (Interval.prod₁ P).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
