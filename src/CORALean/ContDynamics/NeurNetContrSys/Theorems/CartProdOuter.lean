module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.CartProd
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `cartProd` holds every stacked pair

A state `x` of `X` and an input `u` of `Y` stack to `[x; u] = [I; 0] x + [0; I] u`, each summand
in its embedded set by `Mtimes`'s guarantee, the sum in `cartProd X Y` by `Plus`'s. What
[1, Alg. 2] asks of the product.

## Inputs
* `X` – state set
* `Y` – network output set
* `x` – state
* `u` – network output

## Hypotheses
* `hx` – `x` lies in `X`
* `hu` – `u` lies in `Y`

## Conclusion
* the stacked pair lies in the product set

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

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.cartProd_outer (X : S n) (Y : S m) {x : Vec ℝ n} {u : Vec ℝ m}
    (hx : x ∈ construct X) (hu : u ∈ construct Y) : -- --- CONCL ---
    (Fin.append x u : Vec ℝ (n + m)) ∈
      construct (NeurNetContrSys.cartProd X Y) := by -- --- PROOF ---
  -- the two embeddings, summed, are the stacked vector
  have hsum : (Matrix.of fun i j =>
        Fin.append (fun k => (1 : Mat ℝ n n) k j) (fun _ : Fin m => (0 : ℝ)) i) *ᵥ x +
      (Matrix.of fun i j =>
        Fin.append (fun _ : Fin n => (0 : ℝ)) (fun k => (1 : Mat ℝ m m) k j) i) *ᵥ u =
      Fin.append x u := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [← hsum]
  refine Plus.plus_outer _ _ (Set.add_mem_add (Mtimes.mtimes_outer _ _ ?_)
    (Mtimes.mtimes_outer _ _ ?_)) <;>
  · simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ ‹_›

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
