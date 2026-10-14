module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Project
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `project` holds the state coordinates of every point

`[I 0] z` is `z`'s first `n` coordinates, in `project Z` by `Mtimes`'s guarantee. What
[1, Alg. 2] asks of the projection.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.project_outer (Z : S (n + m)) {z : Vec ℝ (n + m)}
    (hz : z ∈ construct Z) :
    (fun k => z (Fin.castAdd m k)) ∈
      construct (NeurNetContrSys.project (n := n) Z) := by -- --- PROOF ---
  -- `[I 0] z` reads the first `n` coordinates
  have hP : (Matrix.of fun i j =>
        Fin.append (fun k => (1 : Mat ℝ n n) i k) (fun _ : Fin m => (0 : ℝ)) j) *ᵥ z =
      fun k => z (Fin.castAdd m k) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.one_apply]
  rw [← hP]
  refine Mtimes.mtimes_outer _ _ ?_
  simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
  exact Set.mem_image_of_mem _ hz

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
