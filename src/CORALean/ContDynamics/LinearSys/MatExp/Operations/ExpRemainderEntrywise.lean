module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `MatExp.expRemainderEntrywise`, the entrywise remainder box

`expRemainderEntrywise`: the box `[-E(Δt,η), E(Δt,η)]` of CORA's `priv_expmRemainder`, entry by
entry, `E(Δt,η) = e^{|A|Δt} − Σ_{i≤η}(|A|Δt)ⁱ/i!` of eq. (18) in [1]. Where `expRemainder` has one
radius for every entry, the bound on a norm, this has the entry's own, so a small entry of `A`
gives a small box. It holds the remainder of `e^{τA}` for every `τ ≤ Δt`
(`abs_expRemainder_entry_le`) with no condition on `η`.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order

## Output
* interval matrix of the exponential remainder at the step, entry by entry

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[-E(Δt,η), E(Δt,η)]`, `E` the entrywise remainder of `e^{|A|Δt}` after order `η`. -/
noncomputable def MatExp.expRemainderEntrywise (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => -MatExp.expRemainderMat A Δt η j k
  sup := fun j k => MatExp.expRemainderMat A Δt η j k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
