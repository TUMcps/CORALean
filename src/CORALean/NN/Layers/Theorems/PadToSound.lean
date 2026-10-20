module

public import CORALean.NN.Layers.Operations.PolyRelaxationPadTo
public import CORALean.NN.Layers.Theorems.Real.EvalPolyPadCoeffs
public import CORALean.NN.Layers.Theorems.ToRealPadCoeffs

@[expose] public section

/-!
# A padded relaxation is sound

Where the degree bound is spent: the padded polynomial is the original one.

## Inputs
* `P` – polynomial relaxation

## Hypotheses
* `h` – the degree is at most the higher degree
* `hP` – relaxation is sound for the activation

## Conclusion
* the padded relaxation is sound for the activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {k M : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.padTo_sound {P : PolyRelaxation 𝕋 k} (h : k ≤ M)
    (hP : P.Sound σ) : (P.padTo M).Sound σ := by -- --- PROOF ---
  refine ⟨fun {l u _t} hl hu => ?_⟩
  have hco : (fun j => toReal ((P.padTo M).coeffs l u j))
      = Real.padCoeffs (fun i => toReal (P.coeffs l u i)) M := by
    funext j
    exact toReal_padCoeffs (P.coeffs l u) M j
  rw [hco, Real.evalPoly_padCoeffs _ h]
  exact hP.sound hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
