module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ContainsPoint
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemExtPolyZonotopeIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# `[p; 0]` is in the extended polynomial zonotope iff `p` is in the set

`-b + A μ(α)` is zero exactly when the constraint
`A μ(α) = b` holds, and the first coordinates are the generators' own: `[p; 0] ∈ pZ` iff
`p ∈ cPZ`, which is [1, Lemma 1]. This is what `@conPolyZono/contains_` means to decide for a
numeric operand.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.containsPoint_iff (cPZ : ConPolyZono (Vec ℝ n)) (p : Vec ℝ n) :
    cPZ.containsPoint p ↔ p ∈ cPZ.construct := by -- --- PROOF ---
  unfold ConPolyZono.containsPoint
  rw [ConPolyZono.mem_extPolyZonotope_iff]
  constructor
  · -- a zero residual is the constraint
    rintro ⟨a, β, ha, hβ, hc, hx⟩
    refine ⟨a, β, ha, hβ, (PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mpr fun i => ?_, hx⟩
    simpa using hc i
  · -- and the constraint is a zero residual
    rintro ⟨a, β, ha, hβ, hs, hx⟩
    refine ⟨a, β, ha, hβ, fun i => ?_, hx⟩
    simpa using (PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mp hs i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
