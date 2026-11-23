module

public import CORALean.NN.Definitions.CrownNet
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The networks of CROWN's backward bound, in floats

`Real.CrownNet` with float weights, boxes and lines, and no activation function: the bound needs
only the lines and the boxes, and what they bound is the exact network. `Images` ties a float
network to an exact one with the same data read as reals and any activation functions, which is
what `CrownNet.backwardBound_le` assumes. `CrownRow` is what the backward pass carries: the row,
the bound `gap` of its rounding error per coordinate, the constant, and the `slack` that the
rounding has cost so far (all zero at nearest, where both directions round alike).

-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic


-- ========================================  MAIN TYPE  ========================================= --

/-- A chain of affine maps `x ↦ W x + b` and element-wise activations, an activation given by its
input box `[l, u]` and its lower and upper lines `sl t + bl`, `su t + bu`. -/
inductive CrownNet (𝕋 : Type) : ℕ → ℕ → Type where
  | nil {n : ℕ} : CrownNet 𝕋 n n
  | linear {n m k : ℕ} (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (rest : CrownNet 𝕋 m k) : CrownNet 𝕋 n k
  | act {n k : ℕ} (l u sl bl su bu : Vec 𝕋 n) (rest : CrownNet 𝕋 n k) : CrownNet 𝕋 n k

/-- The row on a layer's inputs that the backward pass carries: the row, a bound of its rounding
error per coordinate (`gap`, charged at the coordinate's magnitude), the constant, and the
`slack` charged so far. -/
structure CrownRow (𝕋 : Type) (n : ℕ) where
  row : Vec 𝕋 n
  gap : Vec 𝕋 n
  const : 𝕋
  slack : 𝕋

/-- The exact network `R` has `F`'s data read as reals, and any activation functions. -/
inductive CrownNet.Images {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] :
    {n k : ℕ} → CrownNet 𝕋 n k → Real.CrownNet n k → Prop where
  | nil {n : ℕ} : CrownNet.Images (CrownNet.nil (n := n)) Real.CrownNet.nil
  | linear {n m k : ℕ} {W : Mat 𝕋 m n} {b : Vec 𝕋 m} {rest : CrownNet 𝕋 m k}
      {R : Real.CrownNet m k} (h : CrownNet.Images rest R) :
      CrownNet.Images (.linear W b rest)
        (.linear (fun i j => toReal (W i j)) (fun i => toReal (b i)) R)
  | act {n k : ℕ} {l u sl bl su bu : Vec 𝕋 n} {rest : CrownNet 𝕋 n k} {R : Real.CrownNet n k}
      (σ : ℝ → ℝ) (h : CrownNet.Images rest R) :
      CrownNet.Images (.act l u sl bl su bu rest)
        (.act σ (fun i => toReal (l i)) (fun i => toReal (u i)) (fun i => toReal (sl i))
          (fun i => toReal (bl i)) (fun i => toReal (su i)) (fun i => toReal (bu i)) R)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
