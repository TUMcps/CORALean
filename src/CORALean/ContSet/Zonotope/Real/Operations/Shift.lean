module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.shift`

Translation by `-w`, the generators kept and only the center moved: what
[1, Prop. 6]'s `Z − vᵢ` is, ahead of taking any Minkowski difference.
Not `Plus.plus (Zonotope.ofPoint (-w))`, which only encloses — a plain field
update is exact by construction and needs no theorem to say so at the call
site.

## Inputs
* `Z` – zonotope
* `w` – shift vector

## Output
* zonotope translated by `-w`

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z` translated by `-w`: same generators, center moved. -/
def Zonotope.shift (Z : Zonotope α) (w : α) : Zonotope α := { Z with c := Z.c - w }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
