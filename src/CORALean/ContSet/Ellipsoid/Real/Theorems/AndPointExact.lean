import CORALean.ContSet.Ellipsoid.Real.Operations.AndPoint

/-!
# `and_` of an ellipsoid and a point is exact

`E ∩ {p}` is the point `p` as a degenerate ellipsoid when `p ∈ E` and `∅` otherwise: the
denotation of `Ellipsoid.andPoint` equals the intersection, an equality and not an enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The ellipsoid without generators denotes the single point. -/
theorem Ellipsoid.aux_construct_ofPoint (p : Vec ℝ n) :
    (Ellipsoid.ofPoint p).construct = {p} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    simp [Ellipsoid.ofPoint]
  · rintro rfl
    exact Ellipsoid.mem_ofPoint x


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.andPoint_exact (E : Ellipsoid n) (p : Vec ℝ n) :
    ContSet.construct (E.andPoint p) = E.construct ∩ {p} := by -- --- PROOF ---
  unfold Ellipsoid.andPoint
  split_ifs with h
  · rw [WithEmpty.construct_of]
    change (Ellipsoid.ofPoint p).construct = _
    rw [Ellipsoid.aux_construct_ofPoint]
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff]
    constructor
    · rintro rfl; exact ⟨h, rfl⟩
    · exact fun hx => hx.2
  · rw [WithEmpty.construct_empty]
    ext x
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_singleton_iff, false_iff,
      not_and]
    rintro hx rfl
    exact h hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
