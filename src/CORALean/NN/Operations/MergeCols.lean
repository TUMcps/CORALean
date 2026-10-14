module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.NN.Operations.MergeRows

@[expose] public section

/-!
# [1, Prop. 4] at layer `k+1`: boxing the merged neurons' contribution

The linear layer after a merged activation keeps the survivors' columns and pays for the
bucket `B` with a box: `W_{k+1}(·,B) I_k(B)`, the merged neurons' bounds pushed through their
columns, *added* to the layer's error box. [1, Prop. 4] sets `Î'_{k+1}` to it, which is right
only while `I'_{k+1} = [0, 0]`; [1, Alg. 3] runs [1, Alg. 2] on a network already reduced, and
adding it is how [1, Eq. 4] combines several buckets. The product and the sum round outward.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 4] at layer `k+1`: `Ŵ_{k+1} = W_{k+1}(·,B̄)`, `b̂_{k+1} = b_{k+1}`, and the bucket
`B` on the right of `part` paying `W_{k+1}(·,B) I_k(B)` into the error. -/
def ReducedLinear.mergeCols {n₁ n₂ d r : ℕ} (L : ReducedLinear 𝕋 n₁ n₂)
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r)) (I_k : Float.Interval (Vec 𝕋 n₁)) :
    ReducedLinear 𝕋 d n₂ where
  W := L.W.submatrix id part.left
  b := L.b
  I' := Float.Interval.plus L.I'
    (Float.Interval.mtimes (L.W.submatrix id part.right)
      ⟨I_k.inf ∘ part.right, I_k.sup ∘ part.right⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
