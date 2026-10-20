module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ContainsPointSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitGenCover
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeExact

@[expose] public section

/-!
# `containsPointSet` never rejects a point set the polynomial zonotope contains

Contrapositively, `false` proves that some point is outside the set. The converse fails and
is not claimed: `true` says only that every point is inside some enclosure, and an
enclosure is larger than the set, so a point can pass every one and still be outside it.
Nothing here is an exactness claim.

## Inputs
* `pZ` – polynomial zonotope
* `N` – number of points
* `points` – the points
* `splits` – number of splits
* `order` – zonotope reduction order

## Hypotheses
* `h` – every point lies in the set

## Conclusion
* the containment test holds
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every point of the set is in some piece after any number of rounds. -/
theorem PolyZonotope.aux_splitMany_cover (pZ : PolyZonotope (Vec ℝ n)) (k : ℕ) : -- --- CONCL ---
    ∀ x ∈ pZ.construct, ∃ q ∈ pZ.splitMany k, x ∈ q.construct := by -- --- PROOF ---
  induction k with
  | zero => exact fun x hx => ⟨pZ, List.mem_singleton_self _, hx⟩
  | succ k ih =>
    intro x hx
    obtain ⟨q, hq, hxq⟩ := ih x hx
    rcases PolyZonotope.splitGen_cover q hxq with h | h
    · exact ⟨q.splitGen.1, List.mem_flatMap.mpr ⟨q, hq, by simp⟩, h⟩
    · exact ⟨q.splitGen.2, List.mem_flatMap.mpr ⟨q, hq, by simp⟩, h⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.containsPointSet_sound (pZ : PolyZonotope (Vec ℝ n)) {N : ℕ}
    (points : Fin N → Vec ℝ n) (splits order : ℕ)
    (h : ∀ i, points i ∈ pZ.construct) : -- --- CONCL ---
    pZ.containsPointSet points splits order := by -- --- PROOF ---
  intro i
  -- the point is in some piece, whose enclosure the reduced zonotope's polytope contains
  obtain ⟨q, hq, hxq⟩ := PolyZonotope.aux_splitMany_cover pZ splits (points i) (h i)
  refine ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
  rw [Zonotope.vPolytope_exact]
  exact Zonotope.reduceGirard_outer _ _ (PolyZonotope.zonotopeEven_contains q hxq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
