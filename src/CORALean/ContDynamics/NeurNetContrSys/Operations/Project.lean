module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The state coordinates of an extended set, at any representation

[1, Alg. 2] line 7 (equation (5)) and CORA's `project(R_i, 1:obj.nrOfDims)`: a set of `[x; u]`
read at its first `n` coordinates. Written against `Mtimes` alone, as the matrix `[I 0]`, so that
it runs at whichever representation the loop is reached in (`project_outer`).

## Inputs
* `Z` – extended set

## Output
* the set of the first state coordinates

## References

* [1] N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[I 0] Z`, the first `n` coordinates. -/
def NeurNetContrSys.project (Z : S (n + m)) : S n :=
  Mtimes.mtimes (𝕄 := Mat ℝ) (Matrix.of fun i j =>                  -- [I 0]
    Fin.append (fun k => (1 : Mat ℝ n n) i k) (fun _ : Fin m => (0 : ℝ)) j) Z

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
