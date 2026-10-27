module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffCorrected
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerMinkDiffCorrectedLoopSubsetReachSetExact

@[expose] public section

/-!
# The output of the corrected inner algorithm is an inner approximation

The corrected [1, Alg. 1] from a convex `X₀` over `[0, t_end]`, `ω` steps of `Δt = t_end/ω`:
its output `R̂(τ) = ⋃_k R̂(τ_k)` (line 18) holds only states some run from `X₀` reaches at some
`t ∈ [0, t_end]`, which the printed listing ensures and line 16 as printed breaks
(`innerMinkDiff_timeInterval_counterexample`). This is
`innerMinkDiffCorrectedLoop_subset_reachSetExact` at `k = ω`, given every step's certificate
(`IsInnerMinkDiffCorrectedCert`) along the run; the time-point sets `R̂(t_k)` and each `R̂(τ_k)`
are inner approximations by the same theorem at `k ≤ ω`.

## Inputs
* `ops` – set operations
* `zono` – zonotope of a set's center and generators
* `sys` – system
* `u₀` – constant input
* `U` – input set
* `X₀` – initial set
* `tend` – final time
* `ω` – number of steps
* `fuel` – bound per remainder loop

## Hypotheses
* `hu₀` – input in input set
* `hX₀` – initial set convex
* `htend` – final time positive
* `hω` – at least one step
* `hcert` – every step of the run has its certificate

## Conclusion
* the output lies in the exact reachable set over the whole time

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set

variable {n m : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corrected [1, Alg. 1] from a convex `X₀`: `R̂(τ) ⊆ R([0, t_end])`, given every step's
certificate along the run. -/
theorem NonlinearSys.innerMinkDiffCorrected_subset_reachSetExact
    (ops : NonlinearSys.InnerMinkDiffOps n 𝓛) (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n))
    (sys : NonlinearSys n m) (u₀ : Vec ℝ m) (U : Set (Vec ℝ m)) (hu₀ : u₀ ∈ U)
    (X₀ : Set (Vec ℝ n)) (hX₀ : Convex ℝ X₀) {tend : ℝ} (htend : 0 < tend) {ω : ℕ} (hω : 0 < ω)
    (fuel : ℕ)
    (hcert : ∀ j < ω, ∀ (X Y : Set (Vec ℝ n)) (st : NonlinearSys.InnerMinkDiffState n 𝓛),
      NonlinearSys.innerMinkDiffCorrectedLoop ops zono (fun x => sys.f x u₀) (tend / ω) (11 / 10)
        fuel j X₀ ∅ = some (X, Y) →
      NonlinearSys.innerMinkDiffCorrectedStep ops zono (fun x => sys.f x u₀) (tend / ω) (11 / 10)
        fuel X = some st →
      NonlinearSys.IsInnerMinkDiffCorrectedCert sys u₀ (tend / ω) ops zono X st) : -- --- CONCL ---
    ∀ Rτ ∈ NonlinearSys.innerMinkDiffCorrected ops zono (fun x => sys.f x u₀) X₀ tend ω fuel,
      Rτ ⊆ ⋃ t ∈ Icc 0 tend, sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t := by -- --- PROOF ---
  intro Rτ (h : _ = some Rτ)
  -- line 18's union is the second component of the loop's `ω` steps
  unfold NonlinearSys.innerMinkDiffCorrected at h
  obtain ⟨⟨Rtk, Rτ'⟩, hl, rfl⟩ := Option.map_eq_some_iff.mp h
  have hω' : (0 : ℝ) < ω := Nat.cast_pos.mpr hω
  have hk := (NonlinearSys.innerMinkDiffCorrectedLoop_subset_reachSetExact ops zono sys u₀ U hu₀
    (div_pos htend hω') (11 / 10) fuel X₀ hX₀ hcert _ hl).2.2
  -- `ω Δt = t_end`
  rwa [mul_div_cancel₀ tend hω'.ne'] at hk

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
