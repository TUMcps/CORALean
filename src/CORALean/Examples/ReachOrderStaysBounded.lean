import CORALean.ContDynamics.LinearSysDT.Theorems.ReachBigO
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `reach`'s size and its soundness, off the same computed set

`reach_order_le` and `reach_h_isBigO` say the generator count after `k + 1`
steps stays at `o * n`, with no `k` in it — reduction, run once every step, is
what buys that. `reach_outer` says the very same `reach sys o R₀ U` still holds
a concrete trajectory, at any `k`. Both facts are stated of the one computed
set, so the bound is not bought by giving soundness away.

At `k = 0` there is no bound to state: `reach _ _ R₀ U 0` is `R₀` itself, the
caller's own set, never reduced.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

-- The identity on `Vec ℝ 2`, order held at `3`, started at `(1, 1)` with no input.

def Example.rosSys : LinearSysDT ℝ 2 := ⟨(1 : Mat ℝ 2 2)⟩

def Example.rosX0 : Vec ℝ 2 := ![1, 1]
def Example.rosR0 : Zonotope (Vec ℝ 2) := Zonotope.ofPoint Example.rosX0
def Example.rosU : Zonotope (Vec ℝ 2) := Zonotope.ofPoint (0 : Vec ℝ 2)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The generator bound at every step past the first, `o = 3` and `n = 2` fixed
so the right side reads as a number rather than a product. -/
example (k : ℕ) :
    (Example.rosSys.reach (S := 𝒵) ⟨Example.rosR0, Example.rosU, 0, k + 1⟩
      ⟨3, by norm_num⟩).h ≤ 6 :=
  Example.rosSys.reach_order_le (by norm_num) Example.rosR0 Example.rosU k

/-- The same fact restated as growth: the count is `O(1)` in the step index. -/
example :
    (fun k : ℕ => (((Example.rosSys.reach (S := 𝒵) ⟨Example.rosR0, Example.rosU, 0, k + 1⟩
        ⟨3, by norm_num⟩).h : ℕ) : ℝ))
      =O[Filter.atTop] fun _ : ℕ => (1 : ℝ) :=
  Example.rosSys.reach_h_isBigO (by norm_num) Example.rosR0 Example.rosU

/-- A trajectory the identity leaves fixed: the input held at `0`, witnessed by
`Zonotope`'s own `OfPoint`. -/
theorem Example.rosTraj : Example.rosSys.Trajectory (S := 𝒵) Example.rosR0 Example.rosU
    (fun _ => Example.rosX0) (fun _ => 0) where
  init := Zonotope.mem_ofPoint Example.rosX0
  input _ := Zonotope.mem_ofPoint 0
  step _ := by simp [Example.rosSys, Matrix.one_mulVec]

/-- Soundness at the same `o`, `R₀` and `U` the bound above was stated at —
neither fact was bought at the other's expense. -/
example (k : ℕ) :
    Example.rosX0 ∈
      construct (Example.rosSys.reach (S := 𝒵) ⟨Example.rosR0, Example.rosU, 0, k⟩
        ⟨3, by norm_num⟩) :=
  Example.rosSys.reach_outer (S := 𝒵) (by norm_num) Example.rosR0 Example.rosU Example.rosTraj k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
