module

public import CORALean.ContSet.PolyZonotope.Real.Operations.NoIndep
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# What `noIndep` denotes

Exactly the image of the factor cube under `PolyZonotope.point` (the dependent part of the set,
the independent block left aside).

## Inputs
* `α` – ambient type
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is the points over the unit factor box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact: `noIndep` denotes the dependent part, `point` over the factor cube. -/
theorem PolyZonotope.noIndep_construct {α : Type} [AddCommGroup α] [Module ℝ α]
    (pZ : PolyZonotope α) :
    pZ.noIndep.construct =
      {x | ∃ a : Fin pZ.p → ℝ, (∀ k, |a k| ≤ 1) ∧ x = pZ.point a} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨a, β, ha, -, rfl⟩
    exact ⟨a, ha, by simp [PolyZonotope.point, PolyZonotope.noIndep]; rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Fin.elim0, ha, fun j => j.elim0,
      by simp [PolyZonotope.point, PolyZonotope.noIndep]; rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
