module

public import CORALean.ContDynamics.LinearSys.Theorems.HausdorffDist2InputReachRunLe

@[expose] public section

/-!
# [1, Prop. 2]'s eq. (21) at the varying step parameters of `Alg. 2`

`HausdorffDist2InputReachRunLe.lean` solves eq. (21)'s recursion at one `Δt` and one `η`, `Alg. 1`'s
regime. [1] prints eq. (21) with `Alg. 2`'s own `Δt_k` and `η_k`, and so does this: the time
points are `t_k = ∑_{j<k} Δt_j`, step `j` is computed at `(Δt_j, η_j)`, and the accumulated error
is `ε^U_k = ∑_{j<k} Δε^U_j(Δt_j, η_j)`, eq. (25) at `t_j`. The induction is the same as for one
`Δt`, with eq. (24)'s one step (`hausdorffDist₂_inputReach_step_le`, which already takes its own
`Δt` and `η`) as its step.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A finite Minkowski sum of compact nonempty sets is compact and nonempty. -/
theorem aux_isCompact_sum_range_var (f : ℕ → Set (Vec ℝ n)) (hf : ∀ j, IsCompact (f j))
    (hne : ∀ j, (f j).Nonempty) (k : ℕ) :
    IsCompact (∑ j ∈ Finset.range k, f j) ∧
      (∑ j ∈ Finset.range k, f j).Nonempty := by -- --- PROOF ---
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, ← Set.singleton_zero]
    exact ⟨isCompact_singleton, Set.singleton_nonempty 0⟩
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact ⟨ih.1.add (hf k), ih.2.add (hne k)⟩

/-- Nothing has flowed in yet at `t = 0`: the exact particular solution is the origin. -/
theorem aux_inputReach_zero_var (sys : LinearSys 𝕋 n) {U : S n} (hne : (construct U).Nonempty) :
    sys.inputReach U 0 = {0} := by -- --- PROOF ---
  obtain ⟨c, hc⟩ := hne
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨fun _ => c, fun _ _ => hc,
    aestronglyMeasurable_const, (intervalIntegral.integral_same).symm⟩, ?_⟩
  rintro _ ⟨u, -, -, rfl⟩
  exact intervalIntegral.integral_same


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2], eq. (21) at `Alg. 2`'s varying `Δt_k` and `η_k`: with `t_j = ∑_{i<j} Δt_i`, the
distance between the exact particular solution at `t_k` and eq. (20)'s recursively accumulated
outer-approximation is under the summed one-step errors of eq. (25). -/
theorem LinearSys.hausdorffDist₂_inputReach_run_var_le (sys : LinearSys 𝕋 n) {U : S n}
    (Δt : ℕ → ℝ) (η : ℕ → ℕ) (hΔt : ∀ j, 0 < Δt j) (hbdd : Bornology.IsBounded (construct U))
    (hne : (construct U).Nonempty)
    (hcP : ∀ t : ℝ, 0 ≤ t → IsCompact (sys.inputReach U t))
    (hcQΔ : ∀ j, IsCompact
      (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 (Δt j) (η j)))
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (h0 : (0 : Vec ℝ n) ∈ construct U) (k : ℕ) : -- --- STMT ---
    hausdorffDist₂ (sys.inputReach U (∑ i ∈ Finset.range k, Δt i))
        (∑ j ∈ Finset.range k,
          (fun x => exp ((∑ i ∈ Finset.range j, Δt i) • toRealMat sys.A) *ᵥ x)
            '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 (Δt j) (η j))
      ≤ ∑ j ∈ Finset.range k, MatExp.particularSolutionError
          (toRealMat sys.A) (∑ i ∈ Finset.range j, Δt i) (construct U) (Δt j)
          (η j) := by -- --- PROOF ---
  obtain ⟨c, hc⟩ := hne
  have hsum_nn : ∀ j, 0 ≤ ∑ i ∈ Finset.range j, Δt i :=
    fun j => Finset.sum_nonneg fun i _ => (hΔt i).le
  have hQΔne : ∀ j, (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0
      (Δt j) (η j)).Nonempty := fun j =>
    ⟨0, MatExp.zero_mem_particularSolutionOuter _ h0 0 (Δt j) (η j)⟩
  have hcont : ∀ t : ℝ, Continuous (fun x : Vec ℝ n => exp (t • toRealMat sys.A) *ᵥ x) :=
    fun t => (mulVecL (exp (t • toRealMat sys.A))).continuous
  have hsumc := aux_isCompact_sum_range_var
    (fun j => (fun x => exp ((∑ i ∈ Finset.range j, Δt i) • toRealMat sys.A) *ᵥ x)
      '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 (Δt j) (η j))
    (fun j => (hcQΔ j).image (hcont _)) (fun j => (hQΔne j).image _)
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, Finset.sum_range_zero, Finset.sum_range_zero,
      aux_inputReach_zero_var sys ⟨c, hc⟩, ← Set.singleton_zero]
    refine hausdorffDist₂_le_of_mem_dist (le_refl 0) (fun x hx => ?_) (fun x hx => ?_) <;>
      exact ⟨x, hx, by rw [sub_self, norm₂_zero]⟩
  -- one more step of eq. (24), at `t_k = ∑_{i<k} Δt_i`, with that step's own `Δt_k` and `η_k`
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    exact sys.hausdorffDist₂_inputReach_step_le (hsum_nn k) (hΔt k) (η k) hbdd ⟨c, hc⟩
      (hcP _ (hsum_nn k)) (hcP _ (hΔt k).le) (hsumc k).1 (hsumc k).2 (hcQΔ k) ih hconv hclosed h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
