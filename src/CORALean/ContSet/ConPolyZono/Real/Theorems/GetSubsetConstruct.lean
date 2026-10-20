module

public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemGetSubsetIff
public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# `getSubset` represents the subset a factor sub-box reaches

[1, Prop. 14] (`subset`): substituting factor `r` for `cen + rad·α̂ᵣ` restricts its domain to `cen
± rad` and represents the result exactly, an equality and not an enclosure, at every degree the
factor carries in either block. The identity is `PolyZonotope.getSubset_point`'s, read once at the
generators and once at the constraint rows (`PolyLevelSet.mem_getSubset_iff`).

`hrad` makes `cen ± rad` an interval rather than an empty set; `rad = 0` is [1]'s degenerate case,
a factor pinned to a point.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `r` – factor index
* `cen` – center of the subinterval
* `rad` – radius of the subinterval

## Hypotheses
* `hrad` – radius is nonnegative

## Conclusion
* the result is the part of the set on that subinterval

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The subset the factor sub-box `αᵣ ∈ cen ± rad` reaches is exactly what
`getSubset` constructs. -/
theorem ConPolyZono.getSubset_construct (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ)
    (hrad : 0 ≤ rad) : -- --- CONCL ---
    (cPZ.getSubset r cen rad).construct
      = {x | ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ,
            |a r - cen| ≤ rad ∧ (∀ k, k ≠ r → |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
            ∧ (∀ i, (cPZ.cons.op i).holds (cPZ.cons.eval a i))
            ∧ x = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i
                + ∑ j, β j • cPZ.GI j} := by -- --- PROOF ---
  ext x
  -- `p`/`qI` are literally unchanged, so `show` picks that binder type up front
  show (∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ,
        (∀ j, |β j| ≤ 1) ∧ a ∈ (cPZ.getSubset r cen rad).cons.construct
        ∧ x = (cPZ.getSubset r cen rad).c
            + ∑ i, PolyZonotope.monomial (cPZ.getSubset r cen rad).E a i
                • (cPZ.getSubset r cen rad).G i
            + ∑ j, β j • (cPZ.getSubset r cen rad).GI j)
      ↔ _
  constructor
  · -- an unrestricted factor names a point of the sub-box after substitution
    rintro ⟨a, β, hβ, hsat, rfl⟩
    have hgs := (PolyLevelSet.mem_getSubset_iff cPZ.cons r cen rad a).mp hsat
    have ha : ∀ k, |a k| ≤ 1 := (Interval.mem_unit_iff a).mp (cPZ.cons_dom ▸ hgs.1)
    refine ⟨Function.update a r (cen + rad * a r), β, ?_, ?_, hβ, ?_, ?_⟩
    · rw [Function.update_self, add_sub_cancel_left, abs_mul, abs_of_nonneg hrad]
      exact mul_le_of_le_one_right hrad (ha r)
    · intro k hk
      rw [Function.update_of_ne hk]
      exact ha k
    · exact hgs.2
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
    have ha : ∀ k, |a k| ≤ 1 := by
      intro k
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
    refine ⟨a, β, hβ, ?_, ?_⟩
    · refine (PolyLevelSet.mem_getSubset_iff cPZ.cons r cen rad a).mpr
        ⟨cPZ.cons_dom ▸ (Interval.mem_unit_iff a).mpr ha, ?_⟩
      rw [hupdate]
      exact hsat
    · -- the generator identity read backwards, at the recovered witness
      have hgen : (cPZ.toPolyZonotope.getSubset r cen rad).point a
          = cPZ.toPolyZonotope.point a' := by
        rw [← hupdate]
        exact PolyZonotope.getSubset_point cPZ.toPolyZonotope r cen rad a
      exact congrArg (· + ∑ j, β j • cPZ.GI j) hgen.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
