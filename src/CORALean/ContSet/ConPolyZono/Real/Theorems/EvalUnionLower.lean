module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLower
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ProdUnitCol
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalCartProd
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalPadVars
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalSwitch

@[expose] public section

/-!
# The union's lower rows

A row of the first operand's block is its own row at its own factors with the right-hand side
taken at `(1 + α₁) / 2`, and one of the second's at `(1 - α₁) / 2`: `PolyLevelSet.eval_switch`
over `eval_padVars` and `eval_cartProd`, the selector monomial being `α₁` itself.

## Inputs
* `P₁` – constraint of first operand
* `P₂` – constraint of second operand
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the lower rows are each operand's rows weighted by the selector
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {p₁ p₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each operand's rows at its own factors, the right-hand sides weighted by `(1 ± α₁) / 2`. -/
theorem ConPolyZono.eval_unionLower (P₁ : PolyLevelSet p₁) (P₂ : PolyLevelSet p₂)
    (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- CONCL ---
    (ConPolyZono.unionLower P₁ P₂).eval a = Fin.append
      (fun i => (P₁.A *ᵥ PolyZonotope.monomial P₁.R fun k => a (Fin.castAdd 2 (Fin.castAdd p₂ k))) i
        - 2⁻¹ * (1 + a (ConPolyZono.unionSel p₁ p₂)) * P₁.b i)
      (fun i => (P₂.A *ᵥ PolyZonotope.monomial P₂.R fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))) i
        - 2⁻¹ * (1 - a (ConPolyZono.unionSel p₁ p₂)) * P₂.b i) := by -- --- PROOF ---
  funext i
  unfold ConPolyZono.unionLower
  rw [PolyLevelSet.eval_switch, PolyLevelSet.eval_padVars,
    PolyLevelSet.eval_cartProd, ConPolyZono.prod_unitCol, pow_one]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [PolyLevelSet.padVars, PolyLevelSet.cartProd, PolyLevelSet.eval, Fin.append_left,
      Fin.append_right, Pi.sub_apply, if_true, Bool.false_eq_true, if_false] <;> ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
