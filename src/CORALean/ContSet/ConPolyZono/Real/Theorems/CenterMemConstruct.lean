module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.HasNoZeroCol
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialEqZeroOfNoZeroCol
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEqUnit

@[expose] public section

/-!
# A constrained polynomial zonotope with no zero exponent column contains its center

CORA's `center` returns the field `c` with no guarantee. At the factor vector `0` every monomial
vanishes when no exponent column of `E` (and of `R`) is zero, so the point is `c`; the constraint
`A μ(0) = b` then reads `0 = b`. Without these hypotheses `c` need not lie in the set: one
generator `1` with exponent column `0` denotes `{c + 1}`.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* `hE` – exponent matrix has no zero column
* `hR` – constraint exponents have no zero column
* `h0` – constraint offset is zero

## Conclusion
* the center belongs to the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.center_mem_construct (cPZ : ConPolyZono α)
    (hE : ConPolyZono.HasNoZeroCol cPZ.E) (hR : ConPolyZono.HasNoZeroCol cPZ.cons.R)
    (h0 : cPZ.cons.b = 0) : -- --- CONCL ---
    cPZ.center ∈ cPZ.construct := by -- --- PROOF ---
  refine ⟨fun _ => 0, fun _ => 0, fun j => by simp,
    (PolyLevelSet.mem_construct_iff_of_eq_unit cPZ.cons_eq cPZ.cons_dom).mpr
      ⟨fun k => by simp, fun i => ?_⟩, ?_⟩
  · have hm : PolyZonotope.monomial cPZ.cons.R (fun _ => (0 : ℝ)) = 0 :=
      funext fun j => ConPolyZono.monomial_eq_zero_of_noZeroCol hR (fun _ => rfl) j
    simp only [hm, Matrix.mulVec_zero, Pi.zero_apply, h0]
  · simp [ConPolyZono.center, ConPolyZono.monomial_eq_zero_of_noZeroCol hE (fun _ => rfl)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
