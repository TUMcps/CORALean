module

public import CORALean.ContSet.ZonoBundle.Real.Operations.IntervalAll
public import CORALean.ContSet.Interval.Real.Theorems.IntersectionExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `ZonoBundle.intervalAll` contains the bundle

Each member's box holds the whole bundle (`interval_contains`), and the fold keeps whatever every
box held: `Interval.intersection_exact` at each step.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – the bundle has a member

## Conclusion
* the bundle is contained in its box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point every box of the list holds, and the start holds, is in the fold. -/
private theorem ZonoBundle.aux_foldl_intersection (zB : ZonoBundle (Vec ℝ n))
    (L : List (Fin zB.k)) (I : Interval (Vec ℝ n)) {x : Vec ℝ n} (hI : x ∈ I.construct)
    (hL : ∀ i ∈ L, x ∈ (zB.interval i).construct) : -- --- CONCL ---
    x ∈ (L.foldl (fun I i => Interval.intersection I (zB.interval i))
      I).construct := by -- --- PROOF ---
  induction L generalizing I with
  | nil => exact hI
  | cons i L ih =>
    refine ih _ ?_ fun j hj => hL j (List.mem_cons_of_mem _ hj)
    rw [Interval.intersection_exact]
    exact ⟨hI, hL i (List.mem_cons_self ..)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.intervalAll_contains (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.intervalAll hk).construct := fun _ hx =>
  ZonoBundle.aux_foldl_intersection zB _ _ (ZonoBundle.interval_contains zB _ hx)
    fun i _ => ZonoBundle.interval_contains zB i hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
