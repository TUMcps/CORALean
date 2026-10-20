module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `Zonotope.splitKept`

The part `Z_a = ⟨c, G_a⟩` of [1, Sec. IV-B, Step 1)]: the generators
a partition keeps (`part.left`), with the center of `Z`.

## Inputs
* `Z` – zonotope
* `q` – kept count
* `r` – dropped count
* `part` – split of the generator indices

## Output
* zonotope of the kept generators

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⟨c, G_a⟩`, `G_a` the generators `part.left` picks. -/
def Zonotope.splitKept (Z : Zonotope α) {q r : ℕ} (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    Zonotope α :=
  ⟨q, Z.c, fun l => Z.G (part.left l)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
