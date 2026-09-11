import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionDepExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
import CORALean.ContSet.Interval.Real.Theorems.MemPoint

/-!
# `ConPolyZono.intersection` is exactly the intersection

The result is [1, Prop. 11].

The claim the representation exists for, and the one no convex representation
here can make without giving something away.

`intersectionDep_exact` at the zero-width box does the work; `dependent_exact` empties
the independent blocks it asks for, and empties them costlessly.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Translating by the zero-width box is doing nothing, which is what makes
`intersectionDep_exact` at that tolerance the intersection. -/
theorem ConPolyZono.aux_add_point_zero (S : Set (Vec ℝ n)) :
    S + (Interval.point (0 : Vec ℝ n)).construct = S := by -- --- PROOF ---
  have hzero : ∀ z : Vec ℝ n, z ∈ (Interval.point (0 : Vec ℝ n)).construct → z = 0 := by
    intro z hz
    funext i
    have h : (0:ℝ) ≤ z i ∧ z i ≤ 0 := hz i
    show z i = 0
    linarith [h.1, h.2]
  -- both directions, the only member of a zero-width box being `0`
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    have h : y + z = x := hyz
    rw [hzero z hz, add_zero] at h
    rw [← h]
    exact hy
  · intro hx
    exact ⟨x, hx, 0, Interval.mem_point 0, add_zero x⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.intersection_exact (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    cPZ₁.construct ∩ cPZ₂.construct = (cPZ₁.intersection cPZ₂).construct := by
  rw [cPZ₁.dependent_exact, cPZ₂.dependent_exact,
    ← ConPolyZono.aux_add_point_zero cPZ₂.dependent.construct]
  exact ConPolyZono.intersectionDep_exact cPZ₁.dependent cPZ₂.dependent _ rfl rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
