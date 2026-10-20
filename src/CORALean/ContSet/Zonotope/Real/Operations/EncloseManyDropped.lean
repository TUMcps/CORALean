module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `Zonotope.encloseManyDropped`

The axis `encloseMany` leaves out of the standard basis: the one most aligned with
`newGen = direction / ‖direction‖₂` (`h(i) = |newGen' e_i|`, and CORA's sort drops
`ind(end)`). Among several equally aligned axes any maximiser does; CORA drops the last in
its sort order.

Source: [1].

## Inputs
* `direction` – main direction

## Output
* index of its largest entry

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index `encloseMany` leaves out of the standard basis: the entry of `newGen` of largest
magnitude, `ind(end)` of CORA's sort by alignment. -/
noncomputable def Zonotope.encloseManyDropped (direction : Vec ℝ (m + 1)) : Fin (m + 1) :=
  (Finset.exists_max_image Finset.univ
    (fun k => |((Real.sqrt (direction ⬝ᵥ direction))⁻¹ • direction : Vec ℝ (m + 1)) k|)
    ⟨0, Finset.mem_univ _⟩).choose

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
