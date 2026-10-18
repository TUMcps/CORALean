module

public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecEqSum
public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# `getSubset` represents the subset a factor sub-box reaches

[1, Prop. 14] (`subset`): substituting factor `r` for `cen + rad·α̂ᵣ` restricts
its domain to `cen ± rad` and represents the result exactly — an equality, not
an enclosure, at every degree the factor carries in either block. The identity
is `PolyZonotope.getSubset_point`'s, read once at the generators
(`toPolyZonotope`) and once at the constraint columns (`consPolyZonotope`).

`hrad` is what makes `cen ± rad` an interval rather than an empty set, the same
hypothesis `PolyZonotope.getSubset_construct` needs and for the same reason;
the `rad = 0` branch is [1]'s degenerate case, a factor pinned to a point.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The expanded constraint matrix applied to the new factors is the original
one applied to the re-parametrized factors — `getSubset_point` read at the
constraint columns, both sides unfolded to a sum over one coordinate. -/
theorem ConPolyZono.aux_getSubset_mulVec (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ)
    (a : Fin cPZ.p → ℝ) : -- --- STMT ---
    (cPZ.getSubset r cen rad).A *ᵥ PolyZonotope.monomial (cPZ.getSubset r cen rad).R a
      = cPZ.A *ᵥ PolyZonotope.monomial cPZ.R
        (Function.update a r (cen + rad * a r)) := by -- --- PROOF ---
  have hL : (cPZ.getSubset r cen rad).A *ᵥ PolyZonotope.monomial (cPZ.getSubset r cen rad).R a
      = (cPZ.consPolyZonotope.getSubset r cen rad).point a := by
    unfold PolyZonotope.point
    rw [ConPolyZono.mulVec_eq_sum,
      show (cPZ.consPolyZonotope.getSubset r cen rad).c = (0 : Vec ℝ cPZ.m) from rfl, zero_add]
    exact Finset.sum_congr rfl fun x _ => rfl
  have hR : cPZ.A *ᵥ PolyZonotope.monomial cPZ.R (Function.update a r (cen + rad * a r))
      = cPZ.consPolyZonotope.point (Function.update a r (cen + rad * a r)) := by
    unfold PolyZonotope.point
    rw [ConPolyZono.mulVec_eq_sum,
      show cPZ.consPolyZonotope.c = (0 : Vec ℝ cPZ.m) from rfl, zero_add]
    exact Finset.sum_congr rfl fun x _ => rfl
  rw [hL, hR]
  exact PolyZonotope.getSubset_point cPZ.consPolyZonotope r cen rad a

/-- `getSubset`'s own constraint holds at `a` iff the original's holds at the
re-parametrized factors. -/
theorem ConPolyZono.aux_getSubset_holds (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ)
    (a : Fin cPZ.p → ℝ) :
    (cPZ.getSubset r cen rad).satisfies a
      ↔ cPZ.satisfies (Function.update a r (cen + rad * a r)) := by -- --- PROOF ---
  have hmv := ConPolyZono.aux_getSubset_mulVec cPZ r cen rad a
  simp only [ConPolyZono.satisfies, ConPolyZono.holds]
  constructor
  · intro h i
    rw [← hmv]
    exact h i
  · intro h i
    rw [hmv]
    exact h i


-- =======================================  MAIN THEOREM  ======================================= --

/-- The subset the factor sub-box `αᵣ ∈ cen ± rad` reaches is exactly what
`getSubset` constructs. -/
theorem ConPolyZono.getSubset_construct (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ)
    (hrad : 0 ≤ rad) : -- --- STMT ---
    (cPZ.getSubset r cen rad).construct
      = {x | ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ,
            |a r - cen| ≤ rad ∧ (∀ k, k ≠ r → |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
            ∧ cPZ.satisfies a
            ∧ x = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i
                + ∑ j, β j • cPZ.GI j} := by -- --- PROOF ---
  ext x
  -- `p`/`qI` are literally unchanged, so `show` picks that binder type up front
  show (∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ,
        (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1) ∧ (cPZ.getSubset r cen rad).satisfies a
        ∧ x = (cPZ.getSubset r cen rad).c
            + ∑ i, PolyZonotope.monomial (cPZ.getSubset r cen rad).E a i
                • (cPZ.getSubset r cen rad).G i
            + ∑ j, β j • (cPZ.getSubset r cen rad).GI j)
      ↔ _
  constructor
  · -- an unrestricted factor names a point of the sub-box after substitution
    rintro ⟨a, β, ha, hβ, hsat, rfl⟩
    refine ⟨Function.update a r (cen + rad * a r), β, ?_, ?_, hβ, ?_, ?_⟩
    · rw [Function.update_self, add_sub_cancel_left, abs_mul, abs_of_nonneg hrad]
      exact mul_le_of_le_one_right hrad (ha r)
    · intro k hk
      rw [Function.update_of_ne hk]
      exact ha k
    · exact (ConPolyZono.aux_getSubset_holds cPZ r cen rad a).mp hsat
    · exact congrArg (· + ∑ j, β j • cPZ.GI j)
        (PolyZonotope.getSubset_point cPZ.toPolyZonotope r cen rad a)
  · -- inverting the substitution recovers an unrestricted witness
    rintro ⟨a', β, hbox, hunit, hβ, hsat, rfl⟩
    set a : Fin cPZ.p → ℝ := Function.update a' r (if rad = 0 then 0 else (a' r - cen) / rad)
      with ha_def
    -- at zero radius `a' r` is pinned to `cen`; else division by `rad` inverts it
    have hupdate : Function.update a r (cen + rad * a r) = a' := by
      funext k
      rcases eq_or_ne k r with hk | hk
      · rw [hk, Function.update_self, ha_def, Function.update_self]
        rcases eq_or_ne rad 0 with hr0 | hr0
        · rw [hr0] at hbox
          rw [if_pos hr0, mul_zero, add_zero]
          have h0 := abs_nonpos_iff.mp hbox
          linarith
        · rw [if_neg hr0]
          field_simp
          ring
      · rw [Function.update_of_ne hk, ha_def, Function.update_of_ne hk]
    -- `a` lands in the unit box: `a r` by construction, everywhere else by `hunit`
    refine ⟨a, β, ?_, hβ, ?_, ?_⟩
    · intro k
      rcases eq_or_ne k r with hk | hk
      · rw [hk, ha_def, Function.update_self]
        rcases eq_or_ne rad 0 with hr0 | hr0
        · rw [if_pos hr0, abs_zero]
          exact zero_le_one
        · have hrpos : 0 < rad := lt_of_le_of_ne hrad (Ne.symm hr0)
          rw [if_neg hr0, abs_div, abs_of_pos hrpos]
          exact (div_le_one hrpos).mpr hbox
      · rw [ha_def, Function.update_of_ne hk]
        exact hunit k hk
    · have hstep : cPZ.satisfies (Function.update a r (cen + rad * a r)) := by
        rw [hupdate]
        exact hsat
      exact (ConPolyZono.aux_getSubset_holds cPZ r cen rad a).mpr hstep
    · -- the generator identity read backwards, at the recovered witness
      have hgen : (cPZ.toPolyZonotope.getSubset r cen rad).point a
          = cPZ.toPolyZonotope.point a' := by
        rw [← hupdate]
        exact PolyZonotope.getSubset_point cPZ.toPolyZonotope r cen rad a
      exact congrArg (· + ∑ j, β j • cPZ.GI j) hgen.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
