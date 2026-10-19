module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.Exp
public import CORALean.NN.Layers.Operations.SumOffUp

@[expose] public section

/-!
# Softmax's raw lower bound

`(1 + ∑_{j≠i} exp(hi j - lo i))⁻¹` with the denominator overestimated and the reciprocal rounded
down, where `aux_softmaxExpInRange` licenses `expUp`; zero elsewhere.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   08-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `2 ^ k / 2`, each doubling rounded down. -/
def aux_expUpLimit : ℕ → 𝕋
  | 0 => half one
  | k + 1 => addDown (aux_expUpLimit k) (aux_expUpLimit k)

/-- Every term and both additions rounded up. -/
def aux_softmaxDenomUp (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  addUp one (sumOffUp i fun j => expUp k (subUp (I.sup j) (I.inf i)))

/-- Whether `subUp (sup j) (inf i)` is at most `aux_expUpLimit k` for every `j ≠ i`. -/
def aux_softmaxExpInRange (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : Bool :=
  (List.finRange n).all fun j => decide (j = i) || le (subUp (I.sup j) (I.inf i)) (aux_expUpLimit k)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reciprocal of `aux_softmaxDenomUp` rounded down, or zero where `expUp` is not licensed. -/
def softmaxRawLower (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  if aux_softmaxExpInRange k I i = true then divDown one (aux_softmaxDenomUp k I i) else zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
