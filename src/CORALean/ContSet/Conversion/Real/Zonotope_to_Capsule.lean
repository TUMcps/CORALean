module

public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Capsule

@[expose] public section

/-!
# A zonotope as a capsule

CORA's `capsule(zonotope)` takes the SVD basis `B` of `[-G, G]`, encloses `B'Z` by a box, makes the
capsule of that box and maps it back by `B`. Here the basis is the identity: the capsule of
`interval(Z)`. This is the sound instance, an outer enclosure, not CORA's capsule (the rotated
capsule is generally a different, often tighter, set), and nothing here claims equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Zonotope.capsule (Z : Zonotope (Vec ℝ n)) : Capsule n :=
  Z.interval.capsule


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.capsule_contains (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.capsule.construct :=
  subset_trans Z.interval_contains Z.interval.capsule_contains

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
