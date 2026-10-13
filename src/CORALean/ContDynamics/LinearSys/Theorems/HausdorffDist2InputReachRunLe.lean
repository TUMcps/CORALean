module

public import CORALean.ContDynamics.LinearSys.Theorems.HausdorffDist2InputReachStepLe

@[expose] public section

/-!
# [1, Prop. 2]'s eq. (21): the time-point error accumulated over the horizon

Eq. (24)'s one step is `hausdorffDist₂_inputReach_step_le`; this is eq. (21)'s accumulation
of it, `ε^U_k = ∑_{j<k} Δε^U_j(Δt,η)`, and so also eq. (33)'s `ε^a_k` for the same term.

The computed side is eq. (20)'s one-step set propagated and summed,
`P̂^U(t_k) = ⊕_{j<k} e^{At_j}P̂^U(Δt)` — the recursion `P̂^U(t_{k+1}) = P̂^U(t_k) ⊕
e^{At_k}P̂^U(Δt)` of `Alg. 1` line 10 before its reduction, solved. The reduction's own
share is eq. (28) and is accounted separately.

Compactness of the exact solution at each `t_k` is what `Def. 5` asks of everything it
measures, as for the single step. Eq. (20)'s soundness is not assumed: the step uses
`Prop. 11`'s bound for `U₀` convex, closed and containing `0`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
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

/-- A finite Minkowski sum of compact nonempty sets is compact and nonempty, which is what
`hausdorffDist₂_add_le` asks of the accumulated summand at every step. -/
theorem aux_isCompact_sum_range (f : ℕ → Set (Vec ℝ n)) (hf : ∀ j, IsCompact (f j))
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

/-- Nothing has flowed in yet at `t = 0`: the exact particular solution is the origin, the
integral over an empty window. -/
theorem aux_inputReach_zero (sys : LinearSys 𝕋 n) {U : S n} (hne : (construct U).Nonempty) :
    sys.inputReach U 0 = {0} := by -- --- PROOF ---
  obtain ⟨c, hc⟩ := hne
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨fun _ => c, fun _ _ => hc,
    aestronglyMeasurable_const, (intervalIntegral.integral_same).symm⟩, ?_⟩
  rintro y ⟨u, -, -, rfl⟩
  exact intervalIntegral.integral_same


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2], eq. (21): the distance between the exact particular solution at `t_k = kΔt`
and eq. (20)'s recursively accumulated outer-approximation is under the summed one-step
errors of eq. (25). -/
theorem LinearSys.hausdorffDist₂_inputReach_run_le (sys : LinearSys 𝕋 n) {U : S n}
    {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ) (hbdd : Bornology.IsBounded (construct U))
    (hne : (construct U).Nonempty)
    (hcP : ∀ t : ℝ, 0 ≤ t → IsCompact (sys.inputReach U t))
    (hcQΔ : IsCompact (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η))
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (h0 : (0 : Vec ℝ n) ∈ construct U) (k : ℕ) :
    hausdorffDist₂ (sys.inputReach U ((k : ℝ) * Δt))
        (∑ j ∈ Finset.range k, (fun x => exp (((j : ℝ) * Δt) • toRealMat sys.A) *ᵥ x)
          '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η)
      ≤ ∑ j ∈ Finset.range k, MatExp.particularSolutionError
          (toRealMat sys.A) ((j : ℝ) * Δt) (construct U) Δt η := by -- --- PROOF ---
  obtain ⟨c, hc⟩ := hne
  have hQΔne : (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η).Nonempty :=
    ⟨0, MatExp.zero_mem_particularSolutionOuter _ h0 0 Δt η⟩
  have hcont : ∀ t : ℝ, Continuous (fun x : Vec ℝ n => exp (t • toRealMat sys.A) *ᵥ x) :=
    fun t => (mulVecL (exp (t • toRealMat sys.A))).continuous
  have hsumc := aux_isCompact_sum_range
    (fun j => (fun x => exp (((j : ℝ) * Δt) • toRealMat sys.A) *ᵥ x)
      '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η)
    (fun j => hcQΔ.image (hcont _)) (fun j => hQΔne.image _)
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, Finset.sum_range_zero, Nat.cast_zero, zero_mul,
      aux_inputReach_zero sys ⟨c, hc⟩, ← Set.singleton_zero]
    refine hausdorffDist₂_le_of_mem_dist (le_refl 0) (fun x hx => ?_) (fun x hx => ?_) <;>
      exact ⟨x, hx, by rw [sub_self, norm₂_zero]⟩
  -- one more step of eq. (24), at `t_k = kΔt`, added to what the first `k` steps cost
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      show ((k + 1 : ℕ) : ℝ) * Δt = (k : ℝ) * Δt + Δt by push_cast; ring]
    exact sys.hausdorffDist₂_inputReach_step_le (by positivity) hΔt η hbdd ⟨c, hc⟩
      (hcP _ (by positivity)) (hcP _ hΔt.le) (hsumc k).1 (hsumc k).2 hcQΔ ih hconv hclosed h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
