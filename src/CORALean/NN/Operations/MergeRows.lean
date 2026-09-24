import CORALean.Global.Partition
import CORALean.NN.Definitions.ReducibleNetwork

/-!
# [1, Prop. 4] at layer `k-1`: keeping the surviving rows

The linear layer before a merged activation loses the rows of the merged neurons: weights,
bias and error box alike are restricted to the survivors `B̄`, the left of the split. A
selection, so nothing rounds, and the survivors compute exactly what they did.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 4] at layer `k-1`: `Ŵ_{k-1} = W_{k-1}(B̄,·)`, `b̂_{k-1} = b_{k-1}(B̄)`,
`Î'_{k-1} = I'_{k-1}(B̄)`, the survivors `B̄` on the left of `part`. -/
def ReducedLinear.mergeRows {n n₁ d r : ℕ} (L : ReducedLinear 𝕋 n n₁)
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r)) : ReducedLinear 𝕋 n d where
  W := L.W.submatrix part.left id
  b := L.b ∘ part.left
  I' := ⟨L.I'.inf ∘ part.left, L.I'.sup ∘ part.left⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
