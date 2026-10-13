module

public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemErrorSolutionAdaptive

@[expose] public section

/-!
# `errorSolution_adaptive` with a static input

With `Vstat` too: a dynamic point `v` and a static point `s` held over the step contribute
`∫₀^Δt e^{Aσ}dσ (v + s)`, and `Rerror` holds it: `eAtInt Vstat`, the exact orders plus
`E Δt`, takes the static part whole. Outer only, held inputs only, by [1, Lemma 1].

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

theorem LinearSys.expIntegral_mem_errorSolutionAdaptive_static (sys : LinearSys 𝕋 n)
    {Δt : ℝ} (hΔt : 0 ≤ Δt) (η : ℕ) {Vdyn Vstat : S n} {v s : Vec ℝ n}
    (hv : v ∈ construct Vdyn) (hs : s ∈ construct Vstat) :
    MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ v + MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ s
      ∈ construct (sys.errorSolutionAdaptive Δt η Vdyn (some Vstat)) := by -- --- PROOF ---
  set A := toRealMat sys.A
  -- the dynamic part is the case without a static set
  have hdyn := sys.expIntegral_mem_errorSolutionAdaptive hΔt η hv
  -- the static part: the integrated exponential is a member of `eAtInt`
  have hstat : MatExp.expIntegral A Δt *ᵥ s
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.adaptiveIntegral A Δt η) Vstat) := by
    refine Mtimes.mtimes_outer _ _ (Set.mem_biUnion ?_ (Set.mem_image_of_mem _ hs))
    refine Interval.mem_mat_iff.mpr fun j k => ?_
    have hmem := Interval.mem_mat_iff.mp
      (MatExp.expIntegral_sub_sum_mem_adaptiveRemainder A hΔt η) j k
    simp only [MatExp.adaptiveIntegral, MatExp.adaptiveRemainder, Matrix.sub_apply] at hmem ⊢
    constructor <;> linarith [hmem.1, hmem.2]
  simp only [LinearSys.errorSolutionAdaptive] at hdyn ⊢
  exact Plus.plus_outer _ _ (Set.add_mem_add hdyn hstat)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
