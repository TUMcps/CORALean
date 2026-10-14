module

public import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalAll
public import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `ZonoBundle.intervalAll` encloses the bundle

A point of the bundle lies in every member, so in every member's box, and the fold intersects
nothing but boxes that hold it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.intervalAll_contains (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.intervalAll hk).construct := by -- --- PROOF ---
  intro x hx
  have hmem : ∀ i, x ∈ (Zonotope.interval (zB.Z i)).construct := fun i =>
    Zonotope.interval_contains _ (Set.mem_iInter.mp hx i)
  -- every box the fold meets holds `x`, so the running intersection does
  suffices h : ∀ (l : List (Fin zB.k)) (I : Interval (Vec 𝕋 n)), x ∈ I.construct →
      x ∈ (l.foldl (fun I i => Interval.intersection I (Zonotope.interval (zB.Z i))) I).construct
    from
    h _ _ (hmem _)
  intro l
  induction l with
  | nil => exact fun _ hI => hI
  | cons i l ih =>
    intro I hI
    refine ih _ ?_
    rw [Interval.intersection_exact]
    exact ⟨hI, hmem i⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
