module

public import CORALean.NN.Definitions.Basic

@[expose] public section

/-!
# A scalar enclosure, applied entrywise, encloses the entrywise image
The box whose entry `i` is the enclosure of the scalar box `[l i, u i]` contains `f` applied
entrywise to every vector of the box.

## Inputs
* `n` – vector width
* `E` – scalar enclosure
* `f` – scalar function
* `I` – box of the input
* `x` – input point

## Hypotheses
* `hf` – the enclosure encloses the function
* `hx` – point lies in the box

## Conclusion
* the entrywise image lies in the entrywise enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem EnclosesScalar.vec_mem {n : ℕ} {E : Interval 𝕋 → Interval 𝕋} {f : ℝ → ℝ}
    (hf : EnclosesScalar E f) {I : Interval (Vec 𝕋 n)} {x : Vec ℝ n} (hx : x ∈ I.construct) :
    (fun i => f (x i)) ∈ (⟨fun i => (E ⟨I.inf i, I.sup i⟩).inf,
      fun i => (E ⟨I.inf i, I.sup i⟩).sup⟩ : Interval (Vec 𝕋 n)).construct :=
  fun i => hf ⟨I.inf i, I.sup i⟩ (x i) (hx i).1 (hx i).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
