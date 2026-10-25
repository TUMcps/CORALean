module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# `innerAbstrErr`, the abstraction error's solution set of the inner algorithm

(13) of [1]: the set `R̂_err(L) = ⊕_{j=0}^η A^jΔt^{j+1}/(j+1)! L ⊕ E(Δt)ΔtL` that encloses the
solutions of `ẋ = Ax + l`, `l ∈ L`, from `0` at `Δt`, `E(Δt) = [-E(Δt,η), E(Δt,η)]` the
remainder of [2, (20)] (its authors' version; [1] cites arXiv v2, which numbers it (19)). Line 14
of [1, Alg. 1] evaluates it at the remainder `L̂`, line 11 at each guess.

## Inputs
* `η` – Taylor order
* `Δt` – step size
* `A` – linearization matrix
* `L` – Lagrange remainder set

## Output
* the abstraction error's solution set `R̂_err(L)`

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
* [2] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- (13) of [1]: `R̂_err(L) = ⊕_{j=0}^η A^jΔt^{j+1}/(j+1)! L ⊕ E(Δt)ΔtL`, `E` the remainder of
[2, (20)]. -/
noncomputable def NonlinearSys.innerAbstrErr (η : ℕ) (Δt : ℝ) (A : Mat ℝ n n)
    (L : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  -- [2, (20)] E = [-E(Δt,η), E(Δt,η)]
  let E := Real.MatExp.expRemainderInterval A Δt η
  -- (13) ⊕_{j=0}^η A^j Δt^{j+1}/(j+1)! L ⊕ E(Δt) Δt L
  (∑ j ∈ Finset.range (η + 1), (fun l => ((Δt ^ (j + 1) / (j + 1).factorial) • A ^ j) *ᵥ l) '' L)
    + ⋃ M ∈ E, (fun l => (Δt • M) *ᵥ l) '' L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
