module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachSetBound
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetOuter
public import CORALean.Specification.Theorems.HoldsOfOuter
public import CORALean.Specification.Theorems.Separation

@[expose] public section

/-!
# A specification discharged by support evaluations alone

`holds_of_reach` checks a specification on a set the algorithm built; this
checks one without building any set. What is evaluated is `R₀` and `U` along
the directions `c ∘ Aⁱ`, `k + 1` numbers in all, and what comes out is a
guarantee about the trajectory itself.

Unsafe sets only, and one direction only: that is what a separating hyperplane
certifies. A safe set is not of this shape — containment in one needs a bound in
every direction bounding its faces, which is a list of these, not one.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The propagated bound and a bound on the unsafe set along `-c` separate the
two, so no trajectory meets it at step `k`. -/
theorem LinearSysDT.holds_unsafeSet_of_separating (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (b₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct R₀) d)
    (bU : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct U) d)
    {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory R₀ U x u) (k : ℕ)
    {c : Vec ℝ n →ₗ[ℝ] ℝ} {X : Set (Vec ℝ n)} (v : SupportBound X (-c))
    (h : (sys.reachSetBound R₀ U b₀ bU k c).val + v.val < 0) :
    (Specification.unsafeSet X).Holds {x k} :=
  (Specification.unsafeSet X).holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.reachSet_outer R₀ U traj k))
    (Specification.holds_unsafeSet_of_separating (sys.reachSetBound R₀ U b₀ bU k c) v h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
