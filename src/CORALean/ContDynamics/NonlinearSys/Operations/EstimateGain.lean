module

public import CORALean.ContDynamics.NonlinearSys.Operations.InterpGain
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `estimateGain`: the gain at the finite horizon, read back from two radii

Line 16 of [1, Alg. 2]: eq. (56) fixes `φ⁽¹⁾` implicitly, by asking the product `φ(1)·…·φ(λ')` of
eq. (54)'s interpolated gains to equal `λ r⁽ᵛ⁾_abs / r⁽¹⁾_abs`, the two radii the step's two passes
just computed. [1] calls solving it `estimateGain` and says nothing about how. Line 13 of
[2, Alg. 2] is the same equation. How, here, is bisection on `[0,1]`: every factor of the
left-hand side grows with `φ⁽¹⁾`, so the product does, and halving the bracket toward the crossing
converges to the solution. No `Nat.find` and no `Classical.choose`: every decision goes through
the caller's `le`, so a float layer transcribes this and it runs. `fuel` is the number of
halvings.

## Inputs
* `le` – comparison of reals
* `ζδ` – tuning constant
* `lam` – step scaling
* `rabs1` – abstraction radius at the horizon
* `rabsOpt` – abstraction radius at the optimal step
* `scalings` – number of scalings
* `fuel` – number of halvings

## Output
* the gain at the finite horizon

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Halve the bracket toward where `g` crosses `target`, `fuel` times, and hand
back the last midpoint. -/
noncomputable def aux_estimateGainSearch (le : ℝ → ℝ → Bool) (g : ℝ → ℝ) (target : ℝ) :
    ℝ → ℝ → ℕ → ℝ
  | lo, hi, 0 => (lo + hi) / 2
  | lo, hi, k + 1 =>
    let mid := (lo + hi) / 2
    if le (g mid) target then aux_estimateGainSearch le g target mid hi k
    else aux_estimateGainSearch le g target lo mid k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 16: the gain `φ⁽¹⁾` eq. (56) fixes, at the `λ'` the step
size search settled on. -/
noncomputable def estimateGain (le : ℝ → ℝ → Bool) (ζδ lam rabs1 rabsOpt : ℝ)
    (scalings fuel : ℕ) : ℝ :=
  -- 16. eq. (56): the right-hand side
  let target := lam * rabsOpt / rabs1
  -- 16. eq. (56): the left-hand side
  let lhs := fun φ1 => ∏ j ∈ Finset.range scalings,
    interpGain ζδ φ1 j
  -- 16. eq. (56): solve for φ⁽¹⁾ in [0,1]
  aux_estimateGainSearch le lhs target 0 1 fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
