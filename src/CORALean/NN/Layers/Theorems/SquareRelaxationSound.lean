import CORALean.NN.Layers.Operations.SquareRelaxation
import CORALean.NN.Layers.Theorems.OfDerivSound

/-!
# The square relaxation is sound

`Relaxation.ofDeriv_sound` at `σ' x = 2x`: the stored ends `2l` and `2u` bracket it on the box,
the enclosure `a·a` brackets `x²` at every stored value, and the clamp lands the slope in the
bracket.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_squareDerivLo_le (l u : 𝕋) : toReal (squareDerivLo l u) ≤ 2 * toReal l := by
  have := addDown_le_add l l
  rw [squareDerivLo]
  linarith

theorem aux_le_squareDerivHi (l u : 𝕋) : 2 * toReal u ≤ toReal (squareDerivHi l u) := by
  have := add_le_addUp u u
  rw [squareDerivHi]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem squareRelaxation_sound :
    (squareRelaxation (𝕋 := 𝕋)).Sound fun x => x ^ 2 := by -- --- PROOF ---
  refine Relaxation.ofDeriv_sound (fun x => 2 * x) (fun x => ?_)
    ⟨fun a => ?_, fun a => ?_⟩ (fun l u x hl _ => ?_) (fun l u x _ hu => ?_) (fun l u h => ?_)
  · simpa using hasDerivAt_pow 2 x
  · exact mulDown_le_mul a a |>.trans_eq (by ring)
  · exact (mul_le_mulUp a a).trans' (by ring_nf; exact le_rfl)
  · linarith [aux_squareDerivLo_le l u]
  · linarith [aux_le_squareDerivHi l u]
  · have hlu : toReal (squareDerivLo l u) ≤ toReal (squareDerivHi l u) := by
      linarith [aux_squareDerivLo_le l u, aux_le_squareDerivHi l u]
    refine ⟨?_, ?_⟩
    · rw [squareSlope, toReal_maximum]; exact le_max_left _ _
    · rw [squareSlope, toReal_maximum, toReal_minimum]
      exact max_le hlu (min_le_left _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
