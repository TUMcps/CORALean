import CORALean.ContSet.Capsule.Real.Operations.SupportBound
import CORALean.Global.Cost

/-!
# `Capsule.supportBoundCost`

Asserted, not proved: `Operations/SupportBound.lean` bounds `f` over the
capsule by `f c + |f g| + r * ‖w‖₂`, where `w` is `f` read on the `n` basis
vectors. Evaluating `f` is a parameter `cf`, as for `mapCost`: `f c`, `f g` and
the `n` basis evaluations, `n + 2` in all; then `n` squares, `n - 1` additions,
a `sqrt`, an `abs`, a product and two additions, bounded by `2 * n + 5`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.supportBound` costs at `Vec ℝ n`, one evaluation of `f` costing
at most `cf`. -/
def Capsule.supportBoundCost (cf : Cost) (n : ℕ) : Cost := (n + 2) • cf + ⟨2 * n + 5⟩

/-- Monotone in the dimension. -/
theorem Capsule.supportBoundCost_mono {n n' : ℕ} (cf : Cost) (h : n ≤ n') :
    Capsule.supportBoundCost cf n ≤ Capsule.supportBoundCost cf n' := by
  have := Nat.mul_le_mul_right cf.ops (Nat.add_le_add_right h 2)
  simp only [Capsule.supportBoundCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
