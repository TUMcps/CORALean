module

public import CORALean.Specification.STL.Definitions.DiscreteFormula
public import CORALean.Specification.STL.Operations.DFormulaRob

@[expose] public section

/-!
# Satisfaction with zero robustness

[1, Sec. II-C] states `(x, t) ⊨ φ ≡ ρ^φ(x, t) > 0`. With `μ(x₀) = 0` the negated predicate `¬μ`
holds, `¬(μ(x₀) > 0)`, while `ρ^{¬μ}(x, 0) = -μ(x₀) = 0` is not positive. The boundary is where
the robust semantics cannot tell satisfaction from violation; `STL.DFormula.rob_sound` is what
holds. The robust encoding inherits it, [1, Sec. V (correctness)]: `r^{¬μ}_0 = 0` there too.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a formula is satisfied although its robustness is not positive

## References

* [1] [V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and S. A. Seshia.
      "Model Predictive Control with Signal Temporal Logic Specifications". 53rd IEEE Conference on
      Decision and Control, 2014.](../../../../../references/2014/raman-cdc-mpc-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.DFormula.rob_counterexample :
    let φ : STL.DFormula ℝ := .npred id
    let x : ℕ → ℝ := fun _ => 0
    φ.Satisfies x 0 ∧ ¬ 0 < φ.rob x 0 := by
  intro φ x
  simp [φ, x, STL.DFormula.Satisfies, STL.DFormula.rob]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
