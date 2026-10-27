module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `Zonotope.splitDropped`

The part `Z_b = ⟨0, G_b⟩` of [1, Sec. IV-B, Step 1)]: the generators
a partition drops (`part.right`), centered at `0`.

## Inputs
* `Z` – zonotope
* `q` – kept count
* `r` – dropped count
* `part` – split of the generator indices

## Output
* zonotope of the dropped generators at the origin

## References

* [1] [L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters,
      2025.](../../../../../../references/2025/luetzow-lcss-underapprox-order-reduction.md)
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

/-- `⟨0, G_b⟩`, `G_b` the generators `part.right` picks. -/
def Zonotope.splitDropped (Z : Zonotope α) {q r : ℕ}
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Zonotope α :=
  ⟨r, 0, fun l => Z.G (part.right l)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
