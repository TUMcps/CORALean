import CORALean.ContDynamics.LinearSysDT.Cost.Reach
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLe

/-!
# `reach` costs at most `k` worst-case steps

The worked composition, and the point of the whole arrangement: nothing is
asserted here. The leaf counts come from `Zonotope/Real/Cost/`, the generator
count each is evaluated at comes from the size fact `reach_order_le`, and
monotonicity of a count in the operand size is what joins the two. What is left
is induction on the step count.

`hR₀` is the one hypothesis the size facts cannot supply: `reach_order_le`
bounds every set the run produces but not the caller's own `R₀`, which no step
has reduced yet. A caller who reduces it discharges `hR₀` by `reduce_order_le`.

The bound is linear in `k` because `reduce` runs every step; without it the
`plus` would carry `U`'s generators forward and the run would be quadratic.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every set the run holds is at order `o`: `reach_order_le` past the first
step, and the caller's hypothesis at it. -/
theorem LinearSysDT.aux_reach_h_le (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (hR₀ : R₀.h ≤ o * n) :
    ∀ k, (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).h ≤ o * n
  | 0 => hR₀
  | k + 1 => sys.reach_order_le ho R₀ U k

/-- One step at any input size within the order bound costs at most
`reachStepBound`, by monotonicity of the two counts that see a size. -/
theorem LinearSysDT.aux_step_le (n hU o hIn : ℕ) (h : hIn ≤ o * n) :
    Zonotope.mtimesCost n n hIn + Zonotope.plusCost n
        + Zonotope.reduceGirardCost n (hIn + hU) ≤ LinearSysDT.reachStepBound n hU o :=
  Cost.add_le_add (Cost.add_le_add (Zonotope.mtimesCost_mono n n h) le_rfl)
    (Zonotope.reduceGirardCost_mono n (Nat.add_le_add_right h hU))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k` steps cost at most `k` worst-case steps. Assembled from the asserted
per-operation counts and the proved size facts; nothing asserted here. -/
theorem LinearSysDT.reachCost_le (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (hR₀ : R₀.h ≤ o * n) (k : ℕ) :
    sys.reachCost o ho R₀ U k ≤ k • LinearSysDT.reachStepBound n U.h o := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSysDT.reachCost]
  | succ k ih =>
    -- the step's input is the set reached so far, and it is at order `o`
    have hstep := LinearSysDT.aux_step_le n U.h o _ (sys.aux_reach_h_le ho R₀ U hR₀ k)
    have h := Nat.add_le_add (Cost.le_iff.mp ih) (Cost.le_iff.mp hstep)
    refine Cost.le_iff.mpr ?_
    simpa [LinearSysDT.reachCost, Nat.succ_mul] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
