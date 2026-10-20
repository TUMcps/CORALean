module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# Without independent generators the set is the image of the factor cube

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `hq` – no independent generators

## Conclusion
* the set is the image of the factor cube
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With no independent generators the set is the image of the factor cube. -/
theorem PolyZonotope.construct_of_q_zero (pZ : PolyZonotope (Vec ℝ n))
    (hq : pZ.q = 0) : -- --- CONCL ---
    pZ.construct
      = pZ.point '' Set.Icc (fun _ : Fin pZ.p => (-1 : ℝ)) (fun _ => 1) := by -- --- PROOF ---
  -- there is no independent coefficient to choose
  haveI : IsEmpty (Fin pZ.q) := by rw [hq]; infer_instance
  ext x
  constructor
  · rintro ⟨a, β, ha, -, rfl⟩
    exact ⟨a, ⟨fun k => (abs_le.mp (ha k)).1, fun k => (abs_le.mp (ha k)).2⟩, by
      simp [PolyZonotope.point]⟩
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨a, fun _ => 0, fun k => abs_le.mpr ⟨h1 k, h2 k⟩, fun j => (IsEmpty.false j).elim, by
      simp [PolyZonotope.point]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
