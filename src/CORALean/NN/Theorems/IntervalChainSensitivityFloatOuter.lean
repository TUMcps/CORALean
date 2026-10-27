module

public import CORALean.NN.Operations.IntervalChainSensitivityFloat
public import CORALean.NN.Operations.IntervalChainToChain
public import CORALean.NN.Operations.Sensitivity
public import CORALean.NN.Theorems.SensitivityLinear
public import CORALean.NN.Theorems.SensitivityActivation
public import CORALean.NN.Theorems.ScalarEnclosesVecMem
public import CORALean.NN.Definitions.IntervalChainFloatEncloses
public import CORALean.ContSet.Interval.Float.Theorems.MtimesMem
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.DiagonalMem

@[expose] public section

/-!
# The float sensitivity encloses `Chain.sensitivity`

For a float interval chain standing for a smooth real one (`IntervalChain.Encloses`), the
`Chain.sensitivity` of the chain of its layers at every point of the box `X` lies in the box
`IntervalChain.sensitivity` returns. The forward value of a layer lies in the box the float pass
computes, a linear layer's Jacobian is its weights (`Layer.linear_sensitivity`), an activation's the
diagonal of `σ'` (`Layer.activation_sensitivity`), and the product of enclosed matrices is
enclosed (`Interval.matMul_outer`).

## Inputs
* `n` – input width
* `k` – output width
* `c` – float interval chain
* `r` – real interval chain

## Hypotheses
* `hc` – the float chain stands for the real chain
* `hs` – the real chain's activations have the stored derivatives

## Conclusion
* the real sensitivity at every point of a box lies in the float box
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

theorem IntervalChain.sensitivity_outer {n k : ℕ} {c : IntervalChain 𝕋 n k}
    {r : Real.IntervalChain n k} (hc : c.Encloses r) (hs : r.IsSmooth) : -- --- CONCL ---
    ∀ (X : Interval (Vec 𝕋 n)) (x : Vec ℝ n), x ∈ X.construct →
      r.toChain.sensitivity x ∈ (c.sensitivity X).construct := by -- --- PROOF ---
  induction hc with
  | @nil n₀ =>
    -- the identity is the point matrix of the stored diagonal of ones
    intro X x _
    set I₁ : Mat 𝕋 n₀ n₀ := diagonalBlock fun _ => one with hI₁
    have h := Interval.mem_point I₁
    have e : (RealImage.realImage I₁ : Mat ℝ n₀ n₀) = 1 := by
      ext i j
      show toReal (I₁ i j) = (1 : Mat ℝ n₀ n₀) i j
      rw [hI₁]
      rw [toReal_diagonalBlock, Matrix.one_apply]
      simp [Matrix.diagonal_apply, toRealVec, toReal_one]
    show (1 : Mat ℝ n₀ n₀) ∈ (Interval.point I₁).construct
    rw [← e]
    exact h
  | @linear n m k W b c r _ ih =>
    -- the next layer's input lies in the box `W X + b`, its Jacobian is `W`
    intro X x hx
    have hmem : toRealMat W *ᵥ x + toRealVec b ∈
        (Interval.plus (Interval.mtimes W X) ⟨b, b⟩).construct :=
      Interval.plus_outer _ _ (Set.add_mem_add (Interval.mtimes_mem W _ rfl X hx)
        (Interval.mem_point b))
    have h := ih hs _ _ hmem
    have hW := Interval.mem_point W
    simp only [Real.IntervalChain.toChain, Chain.sensitivity, Layer.linear_sensitivity]
    exact Interval.matMul_outer _ _ h hW
  | @act n k σE σ'E σ σ' c r hσ hσ' _ ih =>
    -- the Jacobian is the diagonal of `σ'`, which the stored enclosure bounds
    intro X x hx
    have h := ih hs.2 _ _ (EnclosesScalar.vec_mem hσ hx)
    simp only [Real.IntervalChain.toChain, Chain.sensitivity, Layer.activation_sensitivity hs.1]
    exact Interval.matMul_outer _ _ h
      (Interval.diagonal_mem _ _ _ (EnclosesScalar.vec_mem hσ' hx))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
