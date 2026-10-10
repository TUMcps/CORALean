import CORALean.ContSet.LevelSet.Real.Definitions.TaylorSeries

/-!
# Gradient enclosures

CORA's `levelSet` stores the gradient of its equation as the function handle `der.grad`, which
accepts a box and returns the interval vector `k` that `tightenDomain`'s `'linear'` contractor
divides by. The handle is symbolic differentiation compiled to interval arithmetic; what the
contractor needs of it is only that its value at a box holds the gradient at every point of the
box, and that is the specification here.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `grad(J)` holds `∇f(ξ)` at every `ξ ∈ J`, coordinate by coordinate. -/
def IsGradEnclosure (f : Vec ℝ n → ℝ) (grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)) : Prop :=
  ∀ J : Interval (Vec ℝ n), ∀ ξ ∈ J.construct, ∀ i,
    (grad J).inf i ≤ taylorGrad f ξ i ∧ taylorGrad f ξ i ≤ (grad J).sup i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
