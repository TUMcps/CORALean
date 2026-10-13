module

public import CORALean.ContDynamics.LinearSys.Operations.ErrorSolutionAdaptive
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralSubSumMemAdaptiveRemainder

@[expose] public section

/-!
# `errorSolution_adaptive` holds what a held input contributes

For the dynamic input `Vdyn` alone: at any `v ∈ Vdyn` and any order `η`, `∫₀^Δt e^{Aσ}dσ v`
is in `Rerror`, the exact orders in the Taylor sum and the rest in `E Δt Vdyn`. Outer only,
and for an input held at one point; the time-varying input is not stated here. The bound
is [1, Lemma 1]'s.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.expIntegral_mem_errorSolutionAdaptive (sys : LinearSys 𝕋 n) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (η : ℕ) {Vdyn : S n} {v : Vec ℝ n} (hv : v ∈ construct Vdyn) :
    MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ v
      ∈ construct (sys.errorSolutionAdaptive Δt η Vdyn none) := by -- --- PROOF ---
  set A := toRealMat sys.A
  -- the integrated exponential is its orders up to `η` plus the tail
  have hsplit : MatExp.expIntegral A Δt *ᵥ v
      = (∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i *ᵥ v)
        + (MatExp.expIntegral A Δt - ∑ i ∈ Finset.range (η + 1),
            MatExp.particularCoeff A Δt i) *ᵥ v := by
    rw [← Matrix.sum_mulVec, ← Matrix.add_mulVec]
    congr 1
    abel
  -- each exact order lands in its own term of the Taylor sum
  have hterm : ∀ i, i ≤ η →
      MatExp.particularCoeff A Δt i *ᵥ v
        ∈ construct (Mtimes.mtimes (sys.inputTerm Δt i) Vdyn) := by
    intro i _
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ hv
  -- the tail is a member of the interval matrix
  have htail : (MatExp.expIntegral A Δt - ∑ i ∈ Finset.range (η + 1),
      MatExp.particularCoeff A Δt i) *ᵥ v
        ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.adaptiveRemainder A Δt η) Vdyn) :=
    Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expIntegral_sub_sum_mem_adaptiveRemainder A hΔt η) (Set.mem_image_of_mem _ hv))
  -- `plus` absorbs one term at a time, as the operation builds the sum
  have hsum : ∀ m, m ≤ η → (∑ i ∈ Finset.range (m + 1), MatExp.particularCoeff A Δt i *ᵥ v)
      ∈ construct (sys.inputTaylorSum Δt Vdyn m) := by
    intro m
    induction m with
    | zero => intro _; rw [Finset.sum_range_one]; exact hterm 0 (Nat.zero_le _)
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ]
      exact Plus.plus_outer _ _ (Set.add_mem_add (ih (Nat.le_of_succ_le hm)) (hterm _ hm))
  rw [hsplit]
  exact Plus.plus_outer _ _ (Set.add_mem_add (hsum η le_rfl) htail)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
