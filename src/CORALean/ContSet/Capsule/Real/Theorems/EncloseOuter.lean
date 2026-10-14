module

public import CORALean.ContSet.Capsule.Real.Operations.Enclose
public import CORALean.ContSet.Capsule.Real.Theorems.ConvHullOuter
public import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter

@[expose] public section

/-!
# `Capsule.enclose` encloses the hull of `C` and `M Cplus`

Outer, and of the set the code computes, `M Cplus`: not of the documented `M C ⊕ Cplus`, which
it misses (`Capsule.enclose_cora_counterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The segments between `C` and the image of `Cplus` lie in `Capsule.enclose`. -/
theorem Capsule.enclose_outer (C : Capsule n) (M : Mat ℝ n m) (Cplus : Capsule m) :
    Set.linComb C.construct ((fun y => M.mulVec y) '' Cplus.construct) ⊆
      (C.enclose M Cplus).construct := by
  refine Set.Subset.trans ?_ (Capsule.convHull_outer C (Capsule.mtimes M Cplus))
  rintro _ ⟨y₁, h₁, y₂, h₂, l, hl, rfl⟩
  exact ⟨y₁, h₁, y₂, Capsule.mtimes_outer M Cplus h₂, l, hl, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
