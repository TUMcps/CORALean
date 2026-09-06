import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
import CORALean.ContSet.HPolytope.Real.Operations.TightAt

/-!
# A point no direction is free at is the one its own tight rows name
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point no direction is free at is the one its own tight rows name. -/
theorem HPolytope.basicPoint_tightAt (P : HPolytope (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ P.construct)
    (hpin : ∀ d : Vec ℝ n, (∀ i, P.A i x = P.b i → P.A i d = 0) → (∀ i, P.Ae i d = 0) → d = 0) :
    P.basicPoint (P.tightAt x) = x := by -- --- PROOF ---
  have hspec : ∀ y : Vec ℝ n,
      ((∀ i, P.tightAt x i = true → P.A i y = P.b i) ∧ ∀ i, P.Ae i y = P.be i) → y = x := by
    rintro y ⟨hy, hye⟩
    have hd : ∀ i, P.A i x = P.b i → P.A i (y - x) = 0 := by
      intro i hi
      have : P.A i y = P.b i := hy i (by simp only [HPolytope.tightAt, if_pos hi])
      rw [map_sub, this, hi, sub_self]
    have hde : ∀ i, P.Ae i (y - x) = 0 := by
      intro i
      rw [map_sub, hye i, hx.2 i, sub_self]
    have := hpin (y - x) hd hde
    rwa [sub_eq_zero] at this
  -- uniqueness is what makes the `dif_pos` branch name `x` itself
  have hex : ∃! y : Vec ℝ n,
      (∀ i, P.tightAt x i = true → P.A i y = P.b i) ∧ ∀ i, P.Ae i y = P.be i := by
    refine ⟨x, ⟨fun i hi => ?_, hx.2⟩, hspec⟩
    by_cases h : P.A i x = P.b i
    · exact h
    · rw [HPolytope.tightAt, if_neg h] at hi
      exact absurd hi (by simp)
  rw [HPolytope.basicPoint, dif_pos hex]
  exact hspec _ hex.choose_spec.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
