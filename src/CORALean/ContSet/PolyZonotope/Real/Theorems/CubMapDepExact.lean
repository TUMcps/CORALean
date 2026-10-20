module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.CubEval
public import CORALean.ContSet.PolyZonotope.Real.Theorems.CubMapDepOnExact

@[expose] public section

/-!
# `cubMapDep` is exactly the cubic map

On a set with nothing independent the image of the factors is the image of `P`'s own points,
`cubEval T '' P.construct = (cubMapDep T P).construct`.

## Inputs
* `T` – family of cubic form tensors
* `pZ` – polynomial zonotope

## Hypotheses
* `hq` – no independent generators

## Conclusion
* the cubic image of the set equals the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact where every coefficient is dependent, which `cubMap` arranges. -/
theorem PolyZonotope.cubMapDep_exact (T : Fin m → Fin n → Mat ℝ n n)
    (pZ : PolyZonotope (Vec ℝ n)) (hq : pZ.q = 0) :
    cubEval T '' pZ.construct = (cubMapDep T pZ).construct := by -- --- PROOF ---
  -- with nothing independent the set is exactly the points
  have hc : pZ.construct = pZ.point '' {a : Fin pZ.p → ℝ | ∀ k, |a k| ≤ 1} := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := PolyZonotope.exists_point_of_q_zero pZ hq hx
      exact ⟨a, ha, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact PolyZonotope.point_mem_construct pZ ha
  rw [hc, ← Set.image_comp]
  exact PolyZonotope.cubMapDepOn_exact LinearMap.id LinearMap.id LinearMap.id T pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
