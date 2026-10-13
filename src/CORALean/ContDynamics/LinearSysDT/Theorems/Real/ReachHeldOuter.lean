module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate

@[expose] public section

/-!
# `LinearSysDT.reachHeld` encloses every held run

Induction on the step count, carried as the explicit equation
`x N = Aᴺ x 0 + (∑ i < N, Aⁱ) u` first, membership read off it second: the
matrix identity `∑ i < N + 1, Aⁱ = A * (∑ i < N, Aⁱ) + 1` is `aux_sum_succ`, and
the vector one follows from `Matrix.mulVec_add`/`mulVec_mulVec`.

Only `plus_outer` and `mtimes_outer` are used, matching what `reachHeld` itself
names — no `reduce_outer`, since `reachHeld` calls no `reduce`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Peels the first term off the sum with `Finset.sum_range_succ'`, rewrites it
by `A`, and folds the remaining sum back up with `Finset.mul_sum`. -/
theorem aux_sum_succ (A : Mat ℝ n n) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), A ^ i = A * (∑ i ∈ Finset.range N, A ^ i) + 1 := by
  rw [Finset.sum_range_succ']
  simp only [pow_succ', pow_zero, ← Finset.mul_sum]

omit [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- The closed form itself, proved once so both the base and the step case of
`reachHeld_outer` read membership off it rather than reproving the recursion. -/
theorem aux_x_eq {sys : LinearSysDT ℝ n} {R₀ U : S n} {x : ℕ → Vec ℝ n} {u : Vec ℝ n}
    (h : sys.HeldTrajectory R₀ U x u) (N : ℕ) :
    x N = sys.A ^ N *ᵥ x 0 + (∑ i ∈ Finset.range N, sys.A ^ i) *ᵥ u := by -- --- PROOF ---
  induction N with
  | zero => simp
  | succ N ih =>
    rw [h.step N, toRealMat_real, ih, aux_sum_succ]
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      ← pow_succ']
    abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reachHeld_outer (sys : LinearSysDT ℝ n) (R₀ U : S n)
    {x : ℕ → Vec ℝ n} {u : Vec ℝ n} (h : sys.HeldTrajectory R₀ U x u) (N : ℕ) :
    x N ∈ construct (sys.reachHeld ⟨R₀, U, 0, N⟩) := by
  rw [aux_x_eq h N]
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ h.init)))
    (mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ h.input))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
