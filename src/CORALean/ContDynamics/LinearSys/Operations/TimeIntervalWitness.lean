module

public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetExactEqUnion
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# A time-point lower bound is a time-interval lower bound

[1, Alg. 1 (lower bounds)]'s line 16: the lower bound `ρ(R̲(t_k), ℓ)` computed at a time point
carries straight over to `ρ(R̲(τ_k), ℓ)`, the whole step, because
`timeIntervalReachSetExact_eq_iUnion` makes `reachSetExact` at any `t ∈ [0, r]` a
*subset* of `timeIntervalReachSetExact` over `[0, r]`, and `SupportWitness.mono`
turns a witness for a subset into a witness for the superset it sits in — the
opposite of `LinearSys.timeIntervalBound`, which needs a set-level enclosure
to shrink an upper bound the other way.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `r` – step length
* `t` – time
* `c` – direction
* `w` – support witness at the time

## Hypotheses
* `ht0` – time nonnegative
* `htr` – time within the step

## Output
* support witness for the whole step

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_reachSetExact_subset_timeIntervalReachSetExact
    (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    {r t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    sys.reachSetExact T R₀ U t ⊆ sys.timeIntervalReachSetExact T R₀ U r := by
  rw [sys.timeIntervalReachSetExact_eq_iUnion]
  exact Set.subset_biUnion_of_mem ⟨ht0, htr⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A witness at any time of the step is a witness for the whole step. -/
def LinearSys.timeIntervalWitness (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n) {r t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (w : SupportWitness (sys.reachSetExact T R₀ U t) c) :
    SupportWitness (sys.timeIntervalReachSetExact T R₀ U r) c :=
  w.mono (aux_reachSetExact_subset_timeIntervalReachSetExact sys T R₀ U ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
