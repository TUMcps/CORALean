module

public import CORALean.NN.Operations.GraphNetProductSumFloat
public import CORALean.NN.Theorems.GraphNetProductSumEval
public import CORALean.NN.Theorems.EvaluateGraphEncloses

@[expose] public section

/-!
# `GraphNet.productSum` encloses the sums of the products

The float MatMul network's zonotope holds `∑ᵢ S_j,i y_i y_{k+i}`, `y = A x + a`, for every `x` of
the input set: the network is the image of `Real.GraphNet.productSum` (its product line sound by
`productLine_encloses` at positive `τ` and nonnegative margins), so
`GraphNet.evaluateGraph_encloses` applies, and `Real.GraphNet.productSum_eval` says what the
exact network computes.

## Inputs
* `A` – the factors' maps
* `a` – the factors' offsets
* `S` – the sums of the products
* `p` – the square root's Newton steps
* `τ` – the least scale
* `w₂` – the margin's factor of the centers' product
* `w₁` – the margin's factor of the larger end
* `slots` – whether the product's errors become generators
* `X` – the input set
* `x` – a point of it

## Hypotheses
* `hτ` – the least scale is positive
* `hw₁` – the first margin is nonnegative
* `hw₂` – the second margin is nonnegative
* `hx` – `x` is in `X`

## Conclusion
* the sums of the products are in the network's zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k n o : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GraphNet.productSum_encloses (A : Mat 𝕋 (k + k) n) (a : Vec 𝕋 (k + k))
    (S : Mat 𝕋 o (k + k)) (p : ℕ) {τ w₂ : 𝕋} {w₁ : ℕ → 𝕋} (slots : Bool)
    (hτ : 0 < toReal τ) (hw₁ : ∀ q, 0 ≤ toReal (w₁ q)) (hw₂ : 0 ≤ toReal w₂)
    (X : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n} (hx : x ∈ X.toSet) : -- --- CONCL ---
    (fun j => ∑ i : Fin k, toRealMat S j (Fin.castAdd k i)
        * ((toRealMat A *ᵥ x + toRealVec a) (Fin.castAdd k i)
          * (toRealMat A *ᵥ x + toRealVec a) (Fin.natAdd k i))) ∈
      ((GraphNet.productSum A a S p τ w₂ w₁ slots).evaluateGraph X).toSet := by -- --- PROOF ---
  -- the float network is the exact one's image, its weights read as reals
  suffices hR : (GraphNet.productSum A a S p τ w₂ w₁ slots).Images
      (Real.GraphNet.productSum (toRealMat A) (toRealVec a) (toRealMat S)) by
    have := GraphNet.evaluateGraph_encloses hR X hx
    rwa [Real.GraphNet.productSum_eval] at this
  have h : (GraphNet.productSum A a S p τ w₂ w₁ slots).Images _ :=
    .layer (.product slots hτ hw₁ hw₂) (.layer .identity .done)
  convert h using 1
  -- the zero bias, read as reals
  simp only [Real.GraphNet.productSum, GraphLayer.toReal, Real.GraphNet.layer.injEq,
    Real.GraphLayer.mk.injEq, List.map_nil, true_and, and_true, heq_eq_eq]
  refine ⟨rfl, rfl, funext fun i => ?_⟩
  simp [toRealVec, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
