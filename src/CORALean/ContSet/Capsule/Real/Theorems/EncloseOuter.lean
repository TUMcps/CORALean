import CORALean.ContSet.Capsule.Real.Operations.Enclose
import CORALean.ContSet.Capsule.Real.Theorems.ConvHullOuter
import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter

/-!
# `Capsule.enclose` encloses the hull of `C` and `M Cplus`

Outer, and of the set the code computes, `M Cplus`: not of the documented `M C ⊕ Cplus`, which
it misses (`Capsule.enclose_cora_counterexample`).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The segments between `C` and the image of `Cplus` lie in `Capsule.enclose`. -/
theorem Capsule.enclose_outer (C : Capsule n) (M : Mat ℝ n m) (Cplus : Capsule m) :
    segments C.construct ((fun y => M.mulVec y) '' Cplus.construct) ⊆
      (C.enclose M Cplus).construct := by
  refine Set.Subset.trans ?_ (Capsule.convHull_outer C (Capsule.mtimes M Cplus))
  rintro _ ⟨y₁, h₁, y₂, h₂, l, hl, rfl⟩
  exact ⟨y₁, h₁, y₂, Capsule.mtimes_outer M Cplus h₂, l, hl, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
