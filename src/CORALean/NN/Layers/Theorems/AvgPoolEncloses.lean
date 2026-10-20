module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.AvgPool
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.LinearEncloses
public import CORALean.NN.Layers.Theorems.TapMatMulVec

@[expose] public section

/-!
# What the average pooling layer encloses

The window's sum scaled by the stored weight: at `winv := (k : ℝ)⁻¹` over ℝ, the average.

## Inputs
* `winv` – inverse of the window size
* `tap` – input index of every window position

## Hypotheses
* `htap` – the taps of a window are distinct

## Conclusion
* the layer encloses the averaging map
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- `Matrix` unscoped would make `FloatOps.zero` ambiguous; only `*ᵥ` is wanted
open scoped Matrix
open ContSet Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.avgPool_encloses (winv : 𝕋) (tap : Fin m → Fin k → Fin n)
    (htap : ∀ j, Function.Injective (tap j)) :
    (Layer.avgPool (S := S) winv tap).Encloses
      fun x j => toReal winv * ∑ l, x (tap j l) :=
  (Layer.linear_encloses _ _).congr fun x => funext fun j => by
    show toReal winv * (∑ l, x (tap j l))
      = (toRealMat (tapMat tap fun _ _ => winv) *ᵥ x) j + toRealVec (fun _ => zero) j
    rw [tapMat_mulVec _ _ htap, ← Finset.mul_sum]
    show _ = toReal winv * (∑ l, x (tap j l)) + toReal (zero : 𝕋)
    rw [toReal_zero, add_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
