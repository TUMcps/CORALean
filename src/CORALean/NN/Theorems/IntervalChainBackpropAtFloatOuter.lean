module

public import CORALean.NN.Operations.IntervalChainBackpropAtFloat
public import CORALean.NN.Theorems.IntervalChainBackpropFloatOuter
public import CORALean.NN.Theorems.IntervalChainBackpropDegenerate
public import CORALean.NN.Definitions.IntervalChainFloatEncloses
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float backpropagation at a box encloses `Chain.backprop`

For a float interval chain standing for a smooth real one (`IntervalChain.Encloses`), the real
`Chain.backprop` of the chain of its layers at a point `x` of the box `X` and at a gradient `g` of
the box `G` lies in the box `IntervalChain.backpropAt` returns. The interval backpropagation of
the real chain is `Chain.backprop` on degenerate pairs (`backprop_degenerate`), and the float box
encloses the real interval backpropagation (`IntervalChain.backprop_outer`).

## Inputs
* `n` – input width
* `k` – output width
* `c` – float interval chain
* `r` – real interval chain
* `X` – float box of input points
* `x` – real input point
* `G` – float box of the output gradient
* `g` – real output gradient

## Hypotheses
* `hc` – the float chain stands for the real chain
* `hs` – the real chain's activations have the stored derivatives
* `hx` – the input lies in its box
* `hg` – the gradient lies in its box

## Conclusion
* the real point backpropagation lies in the float box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.backpropAt_outer {n k : ℕ} {c : IntervalChain 𝕋 n k}
    {r : Real.IntervalChain n k} (hc : c.Encloses r) (hs : r.IsSmooth) (X : Interval (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ X.construct) (G : Interval (Vec 𝕋 k)) {g : Vec ℝ k}
    (hg : g ∈ G.construct) : -- --- CONCL ---
    r.toChain.backprop x g ∈ (c.backpropAt X G).construct := by -- --- PROOF ---
  have h := (IntervalChain.backprop_outer hc (X, X)
    (x, x) (G, G) (g, g) hx hx hg hg).1
  rwa [Real.IntervalChain.backprop_degenerate r hs] at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
