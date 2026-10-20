module

public import CORALean.NN.Layers.Operations.SelectMat
public import CORALean.NN.Layers.Theorems.TapMatMulVec

@[expose] public section

/-!
# A selection matrix times a vector

Output `j` is input `sel j`: a stencil of one tap, which is injective trivially, at the
stored `one`.

## Inputs
* `sel` – input read by each output
* `x` – input vector
* `j` – output coordinate

## Hypotheses
* none

## Conclusion
* the selection matrix returns the selected input coordinate
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Matrix
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem selectMat_mulVec (sel : Fin m → Fin n) (x : Vec ℝ n) (j : Fin m) :
    (toRealMat (selectMat (𝕋 := 𝕋) sel) *ᵥ x) j = x (sel j) := by -- --- PROOF ---
  show ((toRealMat (tapMat (fun (j : Fin m) (_ : Fin 1) => sel j) fun _ _ => (one : 𝕋)))
    *ᵥ x) j = _
  rw [tapMat_mulVec _ _ fun _ a b _ => Subsingleton.elim a b, Fin.sum_univ_one]
  show toReal (one : 𝕋) * x (sel j) = _
  rw [toReal_one, one_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
