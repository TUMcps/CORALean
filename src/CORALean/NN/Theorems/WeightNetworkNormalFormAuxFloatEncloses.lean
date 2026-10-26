module

public import CORALean.NN.Operations.WeightNetworkNormalFormAuxFloat
public import CORALean.NN.Operations.WeightNetworkNormalFormAux
public import CORALean.NN.Definitions.WeightNetworkEnclosesFloat
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Definitions.WeightAccEnclosesFloat
public import CORALean.NN.Definitions.WeightLayerEnclosesFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.DiagonalMem
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# The float loop of `getNormalForm` encloses the real one
If a float accumulator and network enclose a real accumulator and network, the float loop's network
encloses the real loop's. By induction on the network: a linear or elementwise affine layer folds
into the accumulators (the products rounded into boxes enclose the real products), an identity
layer is dropped by both, and an activation flushes the accumulators as layers that enclose each
other before the loops restart from nothing fused.

## Inputs
* `acc` – float accumulator
* `acc'` – real accumulator
* `N` – float weight network
* `N'` – real weight network

## Hypotheses
* `hacc` – the float accumulator encloses the real one
* `hN` – the float network encloses the real one

## Conclusion
* the float loop's network encloses the real loop's
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m d k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Folding a linear layer into enclosing accumulators keeps them enclosing: the product of
matrices of the weight boxes and the image of the offset are in the rounded boxes. -/
private theorem aux_pushLinear_encloses {acc : WeightAcc 𝕋 n d} {acc' : CORALean.WeightAcc ℝ n d}
    (h : acc.Encloses acc') {W₂ : Interval (Mat 𝕋 m d)} {W₂' : Mat ℝ m d}
    (hW : W₂' ∈ W₂.construct) {b₂ : Interval (Vec 𝕋 m)} {b₂' : Vec ℝ m}
    (hb : b₂' ∈ b₂.construct) : -- --- CONCL ---
    (acc.pushLinear W₂ b₂).Encloses (acc'.pushLinear W₂' b₂') := by -- --- PROOF ---
  cases acc <;> cases acc' <;> simp only [WeightAcc.Encloses] at h
  · exact ⟨hW, hb⟩
  · -- the fused weights and offset: a product of matrices and an image of the old offset
    obtain ⟨hA, hc⟩ := h
    exact ⟨Interval.matMul_outer _ _ hW hA, Interval.plus_outer _ _ (Set.add_mem_add
      (Interval.mtimesIntervalMat_outer W₂ _ (Set.mem_iUnion₂.mpr ⟨_, hW, _, hc, rfl⟩)) hb)⟩

/-- Folding an elementwise affine layer into enclosing accumulators keeps them enclosing. -/
private theorem aux_pushAffine_encloses {acc : WeightAcc 𝕋 n d} {acc' : CORALean.WeightAcc ℝ n d}
    (h : acc.Encloses acc') {s : Interval (Vec 𝕋 d)} {s' : Vec ℝ d} (hs : s' ∈ s.construct)
    {o : Interval (Vec 𝕋 d)} {o' : Vec ℝ d} (ho : o' ∈ o.construct) : -- --- CONCL ---
    (acc.pushAffine s o).Encloses (acc'.pushAffine s' o') := by -- --- PROOF ---
  -- the diagonal of the scale lies in the box of the stored diagonal blocks
  have hD := Interval.diagonal_mem s.inf s.sup s' hs
  cases acc <;> cases acc' <;> simp only [WeightAcc.Encloses] at h
  · exact ⟨hD, ho⟩
  · obtain ⟨hA, hc⟩ := h
    exact ⟨Interval.matMul_outer _ _ hD hA,
      Interval.plus_outer _ _ (Set.add_mem_add (Interval.times_outer _ _ ⟨s', hs, _, hc, rfl⟩) ho)⟩

/-- Enclosing accumulators emit enclosing layers. -/
private theorem aux_layer_encloses {acc : WeightAcc 𝕋 n d} {acc' : CORALean.WeightAcc ℝ n d}
    (h : acc.Encloses acc') : acc.layer.Encloses acc'.layer := by
  cases acc <;> cases acc' <;> simp only [WeightAcc.Encloses] at h
  · trivial
  · exact h


-- =======================================  MAIN THEOREM  ======================================= --

theorem WeightNetwork.normalFormAux_encloses {acc : WeightAcc 𝕋 n d}
    {acc' : CORALean.WeightAcc ℝ n d} (hacc : acc.Encloses acc') {N : WeightNetwork 𝕋 d k}
    {N' : CORALean.WeightNetwork ℝ d k} (hN : N.Encloses N') : -- --- CONCL ---
    (N.normalFormAux acc).Encloses (N'.normalFormAux acc') := by -- --- PROOF ---
  induction hN generalizing n with
  | nil =>
    -- nothing left: the accumulated map is emitted as it stands
    cases acc <;> cases acc' <;> simp only [WeightAcc.Encloses] at hacc
    · exact .nil
    · exact .cons ⟨hacc.1, hacc.2⟩ .nil
  | cons hL h ih =>
    -- one layer per kind: folded into the accumulator, dropped, or flushed before the restart
    rename_i L L' rest rest'
    cases L <;> cases L' <;> simp only [WeightLayer.Encloses] at hL <;>
      simp only [WeightNetwork.normalFormAux, CORALean.WeightNetwork.normalFormAux]
    · exact ih (aux_pushLinear_encloses hacc hL.1 hL.2)
    · exact ih (aux_pushAffine_encloses hacc hL.1 hL.2)
    · exact ih hacc
    · exact .cons (aux_layer_encloses hacc)
        (.cons (by simpa only [WeightLayer.Encloses] using hL)
          (ih (acc := .id) (acc' := .id) trivial))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
