module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxError
public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrderLoop
public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder

@[expose] public section

/-!
# `Alg. 2` lines 19-22: the zonotope order for one step

Increase the order while `Δε^r_k(ρ)` still exceeds the admissible share `ε^{r,τ}_k`, returning the
first order that clears it. `Δε^r_k(ρ) := err(⟨0,G_red⟩_Z)`, [1, Prop. 4]'s eq. (29) at Girard's
own ranking, is exactly `reduceBoxError`, so this file adds no second copy of that formula. No
invented fuel: past order `Z.h`, `reduceBox` drops nothing (`reduceBoxError` reads `0` there), so
`Z.h + 1` candidates always reach one — a bound the *set* supplies. Neither `Nat.find` nor
`Classical.choose`: the sweep goes through the caller's `le`, as [1, Alg. 2] and
`adaptSetOrderLoop` do.

## Inputs
* `le` – decidable comparison on reals
* `Z` – zonotope
* `εrτ` – admissible error share

## Output
* coarsest order clearing the share, if any

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 20-22: the coarsest order `ρ ≥ 1` at which `Δε^r_k(ρ)` clears the admissible share,
`none` where the sweep reaches `Z.h + 1` without one. -/
noncomputable def Zonotope.autoTuneSetOrder (le : ℝ → ℝ → Bool) (Z : Zonotope (Vec ℝ n))
    (εrτ : ℝ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | ρ, k + 1 =>
    let ρ' := ρ + 1                             -- 21. ρ_k ← ρ_k + 1
    let Δεr := Z.reduceBoxError ρ'               -- 21. Δε^r_k(ρ_k), Prop. 4
    if le Δεr εrτ then some ρ'                   -- 22. until Δε^r_k(ρ_k) ≤ ε^{r,τ}_k
    else Zonotope.autoTuneSetOrder le Z εrτ ρ' k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
