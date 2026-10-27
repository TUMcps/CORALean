module

public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Halving a box

Lines 13-14 of [1, Alg. 1]: the first half of `[x]` along coordinate `β` keeps the lower end and
ends at the midpoint, `x̄_β - rad`; the rest is the second half, from the midpoint up.

## Inputs
* `B` – box
* `β` – coordinate

## Output
* the two halves of the box along that coordinate

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.halveBox (B : Fin n → Interval ℝ) (β : Fin n) :
    (Fin n → Interval ℝ) × (Fin n → Interval ℝ) :=
  let m := ((B β).inf + (B β).sup) / 2
  (Function.update B β ⟨(B β).inf, m⟩, Function.update B β ⟨m, (B β).sup⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
