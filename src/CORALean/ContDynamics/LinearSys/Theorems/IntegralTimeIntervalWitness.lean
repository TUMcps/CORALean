import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimeIntervalReachSetEqUnion
import CORALean.Global.LinProg.API

/-!
# A time-point lower bound is an exact time-interval lower bound

[1, Alg. 1]'s line 16, carried over from `timeIntervalWitness`: `integralReachSet` at any
`t ∈ [0, r]` is a *subset* of `integralTimeIntervalReachSet` over `[0, r]`, by
`integralTimeIntervalReachSet_eq_iUnion`, and `SupportWitness.mono` turns a witness for a
subset into one for the superset it sits in.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_integralReachSet_subset_integralTimeIntervalReachSet
    (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    {r t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    sys.integralReachSet T R₀ U t ⊆ sys.integralTimeIntervalReachSet T R₀ U r := by
  rw [sys.integralTimeIntervalReachSet_eq_iUnion]
  exact Set.subset_biUnion_of_mem ⟨ht0, htr⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A witness at any time of the step is a witness for the whole step. -/
def LinearSys.integralTimeIntervalWitness (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    {r t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (w : SupportWitness (sys.integralReachSet T R₀ U t) c) :
    SupportWitness (sys.integralTimeIntervalReachSet T R₀ U r) c :=
  w.mono (aux_integralReachSet_subset_integralTimeIntervalReachSet sys T R₀ U ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
