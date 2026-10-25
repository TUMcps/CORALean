module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `Zonotope.reduceByDropped`

The generators a partition drops, kept as a zonotope of their own and centered at the origin:
`⟨0, G_red⟩_Z` in [1, Prop. 4], whose `err` is the price one reduction step pays. `reduceByBox` is
this set's box — the shape `reduceBy` actually substitutes — and `err` reads a box off whatever it
is given, so the two have the same `err`. This one is what the paper writes, and it is the
tighter set of the two, so a bound stated against it is the stronger statement. Not a `Reduce`
operation and no class instantiates it: it names the error, not a reduced set.

## Inputs
* `Z` – zonotope
* `part` – split of the generator indices

## Output
* dropped generators centered at the origin

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 4]'s `⟨0, G_red⟩_Z`: the generators the partition drops, centered
at the origin. -/
def Zonotope.reduceByDropped (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Zonotope (Vec ℝ n) where
  h := r
  c := 0
  G := fun l => Z.G (part.right l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
