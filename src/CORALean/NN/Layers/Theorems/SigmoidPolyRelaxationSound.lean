module

public import CORALean.NN.Layers.Operations.SigmoidPolyRelaxation
public import CORALean.NN.Layers.Theorems.AbsSubEvalPolyDerivLe
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.LeSigmoidDerivHi
public import CORALean.NN.Layers.Theorems.OfSamplingSound
public import CORALean.NN.Layers.Theorems.SigmoidDerivLoLe
public import CORALean.NN.Layers.Theorems.SigmoidEnclosureSound

@[expose] public section

/-!
# The polynomial sigmoid relaxation is sound

Where `Real.sigmoid` appears, and the whole of what the assembly owes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidPolyRelaxation_sound (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : 𝕋 → 𝕋 → 𝕋) (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    (sigmoidPolyRelaxation k c dx p).Sound Real.sigmoid :=
  PolyRelaxation.ofSampling_sound (E := sigmoidEnclosure k) (c := c)
    (M := sigmoidPolyDerivBound k c) (dx := dx) (p := p) (sigmoidEnclosure_sound k)
    Real.hasDerivAt_sigmoid fun l u x hx hx' => abs_sub_evalPolyDeriv_le
      (sigmoidDerivLo_le (sigmoidEnclosure_sound k) l u x hx hx')
      (le_sigmoidDerivHi (sigmoidEnclosure_sound k) l u x hx hx') hx hx'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
