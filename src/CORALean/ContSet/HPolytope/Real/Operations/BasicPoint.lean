import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# The point a choice of rows pins down

Choose some of the inequality rows and demand they hold with equality; the
equalities hold anyway. If exactly one point does that, this is it, and
otherwise the choice names nothing and the value is junk — which callers filter
by feasibility rather than by inspecting it.

No matrix is inverted and no basis is extracted. Uniqueness is stated rather
than computed, which is what makes the argument short: a second solution differs
from the first by a direction every chosen row and every equality fails to see,
and at an extreme point there is no such direction.

Noncomputable, and unavoidably so at this layer — whether two reals are equal is
not decidable, so which rows are tight is not either.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}

/-- The rows tight at `x`, as the choice that names `x`. -/
noncomputable def HPolytope.tightAt (P : HPolytope (Vec ℝ n)) (x : Vec ℝ n) : Fin P.m → Bool :=
  fun i => if P.A i x = P.b i then true else false

noncomputable def HPolytope.basicPoint (P : HPolytope (Vec ℝ n)) (σ : Fin P.m → Bool) :
    Vec ℝ n :=
  if h : ∃! y : Vec ℝ n, (∀ i, σ i = true → P.A i y = P.b i) ∧ ∀ i, P.Ae i y = P.be i then
    h.choose
  else 0

/-- A point no direction is free at is the one its own tight rows name. -/
theorem HPolytope.basicPoint_tightAt (P : HPolytope (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ P.construct)
    (hpin : ∀ d : Vec ℝ n, (∀ i, P.A i x = P.b i → P.A i d = 0) → (∀ i, P.Ae i d = 0) → d = 0) :
    P.basicPoint (P.tightAt x) = x := by
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
