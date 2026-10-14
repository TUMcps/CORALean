module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The Cartesian product of a state set and an input set, at any representation

[1, Alg. 2] line 4, `R̂(tᵢ) ← R(tᵢ) × Y`, and CORA's `aux_appendU2X`: the state set and the
network's image stacked as `[x; u]`. Written against `Mtimes` and `Plus` alone, as the two
embeddings `x ↦ [x; 0]` and `u ↦ [0; u]` summed, so that it runs at whichever representation the
loop is reached in; at a zonotope it is CORA's `G = [X.G 0; 0 U.G]`, `U`'s generators appended.
CORA's `aux_appendU2X` also shares `X`'s generators with `U`'s first ones, which keeps the
dependence of the input on the state; that is sound only for an image that keeps them, which
`NeuralNetwork.enclose` does not promise, so the product here is the plain one (`cartProd_outer`).

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

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X × Y` as `[I; 0] X ⊕ [0; I] Y`. -/
def NeurNetContrSys.cartProd (X : S n) (Y : S m) : S (n + m) :=
  Plus.plus
    (Mtimes.mtimes (𝕄 := Mat ℝ) (Matrix.of fun i j =>                -- x ↦ [x; 0]
      Fin.append (fun k => (1 : Mat ℝ n n) k j) (fun _ : Fin m => (0 : ℝ)) i) X)
    (Mtimes.mtimes (𝕄 := Mat ℝ) (Matrix.of fun i j =>                -- u ↦ [0; u]
      Fin.append (fun _ : Fin n => (0 : ℝ)) (fun k => (1 : Mat ℝ m m) k j) i) Y)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
