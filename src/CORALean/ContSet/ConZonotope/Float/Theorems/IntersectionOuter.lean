module

public import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemPadRightNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemPadLeftNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsNominalIff
public import CORALean.ContSet.ConZonotope.Float.Theorems.AnchorSlabOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.MemSlabNominalIff

@[expose] public section

/-!
# `ConZonotope.intersection` over-approximates the intersection

A point of both sets is `y₁ + e₁ = y₂ + e₂` with `yₖ` nominal and `eₖ` in its box. The witness is
`y₁` at the coefficients `[β₁; β₂]` with the first box's `e₁`: each half satisfies its own
constraints, as for `plus`, and the agreement row reads `G₁ β₁ - G₂ β₂ = c₂ - c₁ + e₂ - e₁`, which
the stored slab holds because its ends were rounded outward from the extreme values of `e₂ - e₁`;
the result contains that slab version (`ConZonotope.anchorSlab_outer`).

Outer only. At zero error boxes the two ends still differ by the rounding of `c₂ - c₁`, which the
result pays for in its rows or its box, so it can hold points of neither operand.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Hypotheses
* none

## Conclusion
* the intersection is contained in the result
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intersection_outer (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    cZ₁.construct ∩ cZ₂.construct ⊆ (cZ₁.intersection cZ₂).construct := by -- --- PROOF ---
  intro x hx
  -- the rows as a slab first, which `anchorSlab` contains
  refine ConZonotope.anchorSlab_outer _ _ _ _ ?_
  obtain ⟨⟨y₁, hy₁', e₁, he₁, hx₁⟩, y₂, hy₂', e₂, he₂, hx₂⟩ := hx
  obtain ⟨β₁, hβ₁, hP₁, hy₁⟩ := ConZonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨β₂, hβ₂, hP₂, hy₂⟩ := ConZonotope.mem_nominalSet_iff.mp hy₂'
  have hx₁' : ∀ i, y₁ i + e₁ i = x i := fun i => congrFun hx₁ i
  have hx₂' : ∀ i, y₂ i + e₂ i = x i := fun i => congrFun hx₂ i
  refine ⟨y₁, ConZonotope.mem_nominalSet_iff.mpr ⟨Fin.append β₁ β₂, ?_, ?_, ?_⟩, e₁, he₁, hx₁⟩
  · refine Fin.addCases (fun l => ?_) fun l => ?_
    · rw [Fin.append_left]; exact hβ₁ l
    · rw [Fin.append_right]; exact hβ₂ l
  -- each half its own constraints, then the agreement rows
  · refine HPolytope.mem_stackRows_nominal_iff.mpr
      ⟨HPolytope.mem_stackRows_nominal_iff.mpr ⟨HPolytope.mem_padLeft_nominal_iff.mpr ?_,
        HPolytope.mem_padRight_nominal_iff.mpr ?_⟩, HPolytope.mem_slab_nominal_iff.mpr fun i => ?_⟩
    · rw [blockLeft_append]; exact hP₁
    · rw [blockRight_append]; exact hP₂
    -- the agreement row: the two nominal points differ by exactly `e₂ - e₁`
    · have hrow : (toRealMat (fun i => Fin.append (fun j => cZ₁.G j i) fun j => neg (cZ₂.G j i))
            *ᵥ Fin.append β₁ β₂) i
          = (y₁ i - toReal (cZ₁.c i)) - (y₂ i - toReal (cZ₂.c i)) := by
        rw [hy₁ i, hy₂ i]
        simp only [mulVec, dotProduct, toRealMat, Fin.sum_univ_add, Fin.append_left,
          Fin.append_right, toReal_neg, neg_mul, Finset.sum_neg_distrib]
        ring
      have hb₁ : toReal (cZ₁.I_error.inf i) ≤ e₁ i ∧ e₁ i ≤ toReal (cZ₁.I_error.sup i) := he₁ i
      have hb₂ : toReal (cZ₂.I_error.inf i) ≤ e₂ i ∧ e₂ i ≤ toReal (cZ₂.I_error.sup i) := he₂ i
      have hxi := (hx₁' i).trans (hx₂' i).symm
      -- both ends: the stored bound rounded outward from the extreme `e₂ - e₁`
      refine ⟨?_, ?_⟩
      · show toReal (addDown (subDown (cZ₂.c i) (cZ₁.c i))
            (subDown (cZ₂.I_error.inf i) (cZ₁.I_error.sup i))) ≤ _
        refine le_of_le_of_eq ?_ hrow.symm
        linarith [addDown_le_add (subDown (cZ₂.c i) (cZ₁.c i))
            (subDown (cZ₂.I_error.inf i) (cZ₁.I_error.sup i)),
          subDown_le_sub (cZ₂.c i) (cZ₁.c i),
          subDown_le_sub (cZ₂.I_error.inf i) (cZ₁.I_error.sup i), hb₁.2, hb₂.1]
      · show _ ≤ toReal (addUp (subUp (cZ₂.c i) (cZ₁.c i))
            (subUp (cZ₂.I_error.sup i) (cZ₁.I_error.inf i)))
        refine le_of_eq_of_le hrow ?_
        linarith [add_le_addUp (subUp (cZ₂.c i) (cZ₁.c i))
            (subUp (cZ₂.I_error.sup i) (cZ₁.I_error.inf i)),
          sub_le_subUp (cZ₂.c i) (cZ₁.c i),
          sub_le_subUp (cZ₂.I_error.sup i) (cZ₁.I_error.inf i), hb₁.1, hb₂.2]
  -- the second generator block is zero, so the point is the first operand's
  · intro i
    rw [hy₁ i]
    show _ = toReal (cZ₁.c i)
      + ∑ j : Fin (cZ₁.h + cZ₂.h),
          toReal (Fin.append cZ₁.G (fun _ _ => (zero : 𝕋)) j i) * Fin.append β₁ β₂ j
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
      Finset.sum_const_zero, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
