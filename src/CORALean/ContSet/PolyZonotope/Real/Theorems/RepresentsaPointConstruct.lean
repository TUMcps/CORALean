module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

@[expose] public section

/-!
# A polynomial zonotope without generators is a point

With every generator `0` the dependent part is `c` at every factor vector and the independent block
adds nothing, so the set is `{c}` (nonempty: `point_mem_construct`). Sufficient only: a set can be
a point with nonzero generators that cancel (`g α` and `-g α`).

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `h` – all generators vanish

## Conclusion
* the set is the singleton of the center
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.construct_eq_of_representsa_point (pZ : PolyZonotope α)
    (h : pZ.representsa_point) : -- --- CONCL ---
    pZ.construct = {pZ.c} := by -- --- PROOF ---
  ext x
  constructor
  · -- every term is `0`, so the point is the center
    rintro ⟨a, β, -, -, rfl⟩
    simp [h.1, h.2]
  · -- the center is the point at the factors `0`
    rintro rfl
    have := pZ.point_mem_construct (a := fun _ => 0) fun _ => by simp
    simpa [PolyZonotope.point, h.1] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
