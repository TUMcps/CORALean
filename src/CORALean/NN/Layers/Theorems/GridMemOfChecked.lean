module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.GridChecked
public import CORALean.NN.Layers.Theorems.AllOverApply

@[expose] public section

/-!
# A checked grid samples inside the box

What the mean value theorem between a sample and a point of the box needs.

## Inputs
* `p` – proposed sample points
* `l` – lower end of the box
* `u` – upper end of the box
* `dx` – maximal gap between samples
* `i` – sample index

## Hypotheses
* `h` – the grid is checked

## Conclusion
* the sample lies inside the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem grid_mem_of_checked {p : Fin (N + 1) → 𝕋} {l u dx : 𝕋}
    (h : gridChecked p l u dx) (i : Fin (N + 1)) :
    toReal l ≤ toReal (p i) ∧ toReal (p i) ≤ toReal u := by
  simp only [gridChecked, Bool.and_eq_true] at h
  have hi := allOver_apply _ h.2 i
  rw [Bool.and_eq_true] at hi
  exact ⟨toReal_le_of_le hi.1, toReal_le_of_le hi.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
