import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap
import CORALean.ContSet.VPolytope.Float.Operations.MemColumnGap
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

/-!
# A zonotope as its corners, over a floating-point scalar

Each of the `2ʰ` corners is a sum over the generators, so each rounds. The
stored vertex is the rounded-down corner and the gap up to the rounded-up one
goes into the error box — the pattern this layer already uses whenever it stores
a whole list at once, since one box has to cover every column.

The zonotope's own error box is added to that gap rather than replacing it: the
corner enclosure and the incoming error are separate debts and both have to be
paid.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The generator's contribution to a corner, at its own sign. -/
def Zonotope.signed (Z : Zonotope (Vec 𝕋 n)) (σ : Fin Z.h → Bool) (i : Fin n) (j : Fin Z.h) : 𝕋 :=
  if σ j then Z.G j i else neg (Z.G j i)

def Zonotope.cornerLo (Z : Zonotope (Vec 𝕋 n)) (l : Fin (2 ^ Z.h)) (i : Fin n) : 𝕋 :=
  addDown (Z.c i) (sumDown (Z.signed (signEquiv Z.h l) i))

def Zonotope.cornerHi (Z : Zonotope (Vec 𝕋 n)) (l : Fin (2 ^ Z.h)) (i : Fin n) : 𝕋 :=
  addUp (Z.c i) (sumUp (Z.signed (signEquiv Z.h l) i))

def Zonotope.vPolytope (Z : Zonotope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) where
  k := 2 ^ Z.h
  V := Z.cornerLo
  E := (VPolytope.columnGap Z.cornerLo Z.cornerHi).plus Z.E


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the exact layer's corner is, in this layer's own fields. -/
theorem Zonotope.aux_signed_toReal (Z : Zonotope (Vec 𝕋 n)) (σ : Fin Z.h → Bool) (i : Fin n)
    (j : Fin Z.h) :
    toReal (Z.signed σ i j) = (if σ j then (1:ℝ) else -1) * toReal (Z.G j i) := by
  rw [Zonotope.signed]
  by_cases h : σ j = true
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, toReal_neg, neg_one_mul]

theorem Zonotope.aux_corner_mem (Z : Zonotope (Vec 𝕋 n)) (l : Fin (2 ^ Z.h)) (i : Fin n) :
    toReal (Z.cornerLo l i)
        ≤ (InflatedContSet.nominal Z).corner (signEquiv Z.h l) i
      ∧ (InflatedContSet.nominal Z).corner (signEquiv Z.h l) i
        ≤ toReal (Z.cornerHi l i) := by -- --- PROOF ---
  -- the exact corner as a sum of signed generators, which the two roundings bracket
  have hval : (InflatedContSet.nominal Z).corner (signEquiv Z.h l) i
      = toReal (Z.c i) + ∑ j, toReal (Z.signed (signEquiv Z.h l) i j) := by
    show toReal (Z.c i) + (∑ j, (if signEquiv Z.h l j then (1:ℝ) else -1) •
      (fun i => toReal (Z.G j i) : Vec ℝ n)) i = _
    rw [Finset.sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => (Z.aux_signed_toReal _ i j).symm)
  rw [hval]
  constructor
  · exact le_trans (addDown_le_add _ _)
      (add_le_add le_rfl (sumDown_le_sum (Z.signed (signEquiv Z.h l) i)))
  · exact le_trans (add_le_add le_rfl (sum_le_sumUp (Z.signed (signEquiv Z.h l) i)))
      (add_le_addUp _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.vPolytope_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.vPolytope.construct := by -- --- PROOF ---
  -- the exact corners, and the rounded ones actually stored
  have hstep : (InflatedContSet.nominal Z).vPolytope.construct
      ⊆ InflatedContSet.nominalSet Z.vPolytope
        + (VPolytope.columnGap Z.cornerLo Z.cornerHi).construct := by
    refine Real.VPolytope.construct_subset_add _ _ (Real.Interval.convex_construct _) fun l => ?_
    exact VPolytope.mem_columnGap fun i => Z.aux_corner_mem l i
  intro x hx
  obtain ⟨p, hp, e, he, rfl⟩ := hx
  obtain ⟨v, hv, g, hg, hvg⟩ := hstep (Real.Zonotope.vPolytope_contains _ hp)
  refine ⟨v, hv, g + e, ?_, ?_⟩
  · exact Interval.plus_outer _ _ ⟨g, hg, e, he, rfl⟩
  · -- the sum's membership destructs into a redex, which `rw` will not match
    have hvg' : v + g = p := hvg
    show v + (g + e) = p + e
    rw [← add_assoc, hvg']

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
