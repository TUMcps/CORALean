module

public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachInnerMinkdiffSubsetReachSetExact

@[expose] public section

/-!
# CORA's `'minkdiff'` inner reachability: the result is inside the reachable set

The whole result of `reachInnerMinkdiff`, CORA's `nonlinearSys/reachInner` with `'minkdiff'` as
CORALean computes it, all time-point and time-interval cells together, lies in the reachable
set over the horizon `R([0, steps Δt]) = ⋃_t R(t)` [1, Def. 1]: each cell lies in the reachable
set at its own times, which are in the horizon, and the cells past it are empty
(`reachInnerMinkdiff_subset_reachSetExact`).

## Inputs
* `ops` – set operations
* `sys` – system
* `u₀` – constant input
* `U` – input set
* `Δt` – step size
* `steps` – number of steps
* `fuel` – bound per error loop
* `X₀` – initial set
* `timePoint` – time-point cells
* `timeInt` – time-interval cells

## Hypotheses
* `hu₀` – input in input set
* `hΔt` – step size nonnegative
* `hcert` – every step has its certificate
* `h` – reachability returned these cells

## Conclusion
* every cell lies in the reachable set over the horizon

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set

variable {n m : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `reachInner` with `'minkdiff'`: every cell lies in `R([0, steps Δt])`, given
`Prop. 1`'s hypotheses at every step. -/
theorem NonlinearSys.reachInnerMinkdiff_subset_reachSetExact_horizon
    (ops : NonlinearSys.LinReachInnerOps n 𝓛) (sys : NonlinearSys n m) (u₀ : Vec ℝ m)
    (U : Set (Vec ℝ m)) (hu₀ : u₀ ∈ U) {Δt : ℝ} (hΔt : 0 ≤ Δt) (steps fuel : ℕ)
    (X₀ : Set (Vec ℝ n))
    (hcert : ∀ (T : ℝ) (X : Set (Vec ℝ n)) (e : Vec ℝ n) (st : NonlinearSys.LinReachInnerState n 𝓛),
      X ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 T) X₀ {u₀} T →
      NonlinearSys.linReachInner ops (fun x => sys.f x u₀) Δt fuel X e = some (some st) →
      NonlinearSys.IsLinReachInnerCert sys u₀ Δt X st)
    {timePoint timeInt : ℕ → Set (Vec ℝ n)}
    (h : NonlinearSys.reachInnerMinkdiff ops (fun x => sys.f x u₀) X₀ Δt steps fuel =
      some (timePoint, timeInt)) : -- --- CONCL ---
    (⋃ k, timePoint k) ∪ (⋃ k, timeInt k) ⊆ ⋃ t ∈ Icc 0 (steps * Δt),
      sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t := by -- --- PROOF ---
  obtain ⟨htp, hti, htp0, hti0⟩ :=
    NonlinearSys.reachInnerMinkdiff_subset_reachSetExact ops sys u₀ U hu₀ hΔt steps fuel X₀ hcert h
  refine union_subset (iUnion_subset fun k => ?_) (iUnion_subset fun k => ?_)
  · -- a time-point cell at `k Δt ≤ steps Δt`
    rcases le_or_gt k steps with hk | hk
    · refine (htp k).trans (subset_biUnion_of_mem (u := fun t =>
        sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t) ⟨by positivity, ?_⟩)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔt
    · rw [htp0 k hk]; exact empty_subset _
  · -- a time-interval cell in `[k Δt, (k+1) Δt] ⊆ [0, steps Δt]`
    rcases lt_or_ge k steps with hk | hk
    · refine (hti k).trans (biUnion_subset_biUnion_left fun t ht =>
        ⟨le_trans (by positivity) ht.1, ht.2.trans ?_⟩)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hΔt
    · rw [hti0 k hk]; exact empty_subset _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
