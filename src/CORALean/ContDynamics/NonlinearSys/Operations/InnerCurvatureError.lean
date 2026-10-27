module

public import CORALean.Specification.STL.Operations.DepCurvatureF
public import CORALean.Specification.STL.Operations.DepCurvatureG
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# `innerCurvatureError`, the curvature error of the inner algorithm

(17) of [1]: the curvature error `C = F box(X₀) ⊕ G w` of the affine solution over `[0, Δt]`,
`F` and `G` the interval matrices of [2, (19), (28)] (its authors' version; [1] cites arXiv v2,
which numbers (19), (28) as (18), (26)). `B` is the box of the start set, shifted to the
linearization point, as line 6 of [1, Alg. 1] passes it.

## Inputs
* `η` – Taylor order
* `Δt` – step size
* `A` – linearization matrix
* `B` – shifted box of start set
* `w` – constant input of linearization

## Output
* the curvature error `C`

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
* [2] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
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

/-- (17) of [1]: the curvature error `C = F box(X₀) ⊕ G w` at the shifted box `B`, `F`, `G` of
[2, (19), (28)]. -/
noncomputable def NonlinearSys.innerCurvatureError (η : ℕ) (Δt : ℝ) (A : Mat ℝ n n)
    (B : Set (Vec ℝ n)) (w : Vec ℝ n) : Set (Vec ℝ n) :=
  -- [2, (19)] F
  let F := STL.depCurvatureF A Δt η
  -- [2, (28)] G
  let G := STL.depCurvatureG A Δt η
  -- (17) C = F box(X₀) ⊕ G w
  (⋃ M ∈ F.construct, (fun x => M *ᵥ x) '' B) + ⋃ N ∈ G.construct, {N *ᵥ w}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
