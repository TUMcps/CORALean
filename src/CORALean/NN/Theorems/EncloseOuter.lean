module

public import CORALean.NN.Definitions.Encloses
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# `NeuralNetwork.enclose` contains the image

Induction on `Encloses`, applying each layer'S own obligation in the order `enclose` applies the
layers. Nothing else is used, so a new layer buys into the whole pipeline by proving
`Layer.Encloses` and nothing more. The enclosure degrades monotonically: each layer encloses the
image of what it was handed, never of the exact set, so the error a layer introduces is carried by
every layer after it. [1, Alg. 1]'S own postcondition, `PZ ⊇ Y`, proved once for any network rather
than only the quadratic-approximation layers the algorithm itself builds.

## Inputs
* `n` – input width
* `m` – output width
* `nn` – network
* `f` – map the network encloses

## Hypotheses
* `hf` – the network encloses the map

## Conclusion
* the map of every point of an input set lies in the enclosure

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike

variable {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.Encloses.enclose_outer {n m : ℕ} {nn : NeuralNetwork ContSet n m}
    {f : Vec ℝ n → Vec ℝ m} (hf : nn.Encloses f) : -- --- CONCL ---
    ∀ (S : ContSet n) (x : Vec ℝ n), x ∈ toSet S →
      f x ∈ toSet (nn.enclose S) := by -- --- PROOF ---
  induction hf with
  | output h =>
      intro _ x hx
      rw [h x]
      exact hx
  | layer hL _ h ih =>
      intro S x hx
      rw [h x]
      exact ih _ _ (hL.enclose_outer S x hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
