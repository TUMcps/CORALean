module

public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import CORALean.ContSet.Taylm.Real.Definitions.Box

@[expose] public section

/-!
# The two halves cover the box

A point of the box lies in the first half if its `β`-coordinate is at most the midpoint, and in the
second otherwise; the other coordinates are untouched.

## Inputs
* `B` – box
* `β` – coordinate
* `t` – point

## Hypotheses
* `ht` – point lies in the box

## Conclusion
* the point lies in one of the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.halveBox_cover {B : Fin n → Interval ℝ} (β : Fin n) {t : Vec ℝ n}
    (ht : Taylm.IsInBox B t) : -- --- CONCL ---
    Taylm.IsInBox (Taylm.halveBox B β).1 t ∨
      Taylm.IsInBox (Taylm.halveBox B β).2 t := by -- --- PROOF ---
  rcases le_total (t β) (((B β).inf + (B β).sup) / 2) with h | h
  · left
    intro k
    by_cases hk : k = β
    · subst hk; simp only [Taylm.halveBox, Function.update_self]; exact ⟨(ht k).1, h⟩
    · simp only [Taylm.halveBox, Function.update_of_ne hk]; exact ht k
  · right
    intro k
    by_cases hk : k = β
    · subst hk; simp only [Taylm.halveBox, Function.update_self]; exact ⟨h, (ht k).2⟩
    · simp only [Taylm.halveBox, Function.update_of_ne hk]; exact ht k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
