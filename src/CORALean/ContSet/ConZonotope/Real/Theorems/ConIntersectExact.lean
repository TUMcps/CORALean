module

public import CORALean.ContSet.ConZonotope.Real.Operations.ConIntersect
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `conIntersect` is exactly the preimage intersection

`{z ∈ cZ₁ | M z ∈ cZ₂}` is the constrained zonotope `conIntersect` builds, an equality
[1, Prop. 1]. Each block keeps its own polytope, and the new rows say that the image of the
first point and the second point agree coordinate by coordinate, which is what `M z ∈ cZ₂` means.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope
* `M` – map from the first into the second space

## Hypotheses
* none

## Conclusion
* the result is exactly the constrained intersection

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The image rows are all that `conIntersect` adds over the two blocks' own constraints. -/
theorem ConZonotope.aux_mem_conIntersect_P_iff (cZ₁ : ConZonotope (Vec ℝ n))
    (cZ₂ : ConZonotope (Vec ℝ m)) (M : Mat ℝ m n)
    (β : Vec ℝ (cZ₁.conIntersect cZ₂ M).h) : -- --- CONCL ---
    β ∈ (cZ₁.conIntersect cZ₂ M).P.construct ↔
      (blockLeft cZ₁.h cZ₂.h β ∈ cZ₁.P.construct
        ∧ blockRight cZ₁.h cZ₂.h β ∈ cZ₂.P.construct)
      ∧ ∀ i, (∑ j, (M *ᵥ cZ₁.G j) i * β (Fin.castAdd cZ₂.h j))
          - ∑ j, cZ₂.G j i * β (Fin.natAdd cZ₁.h j)
          = cZ₂.c i - (M *ᵥ cZ₁.c) i := by -- --- PROOF ---
  constructor
  · intro h
    obtain ⟨hblocks, heqs⟩ := HPolytope.mem_intersection_iff.mp h
    refine ⟨HPolytope.mem_intersection_iff.mp hblocks, fun i => ?_⟩
    have := HPolytope.mem_eqs_iff.mp heqs i
    rw [← this]
    show _ = ∑ j : Fin (cZ₁.h + cZ₂.h), _ * β j
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · rintro ⟨hblocks, heqs⟩
    refine HPolytope.mem_intersection_iff.mpr
      ⟨HPolytope.mem_intersection_iff.mpr hblocks, HPolytope.mem_eqs_iff.mpr fun i => ?_⟩
    rw [← heqs i]
    show ∑ j : Fin (cZ₁.h + cZ₂.h), _ * β j = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Only the first generator block survives; the second is pinned to it. -/
theorem ConZonotope.aux_value_conIntersect (cZ₁ : ConZonotope (Vec ℝ n))
    (cZ₂ : ConZonotope (Vec ℝ m)) (M : Mat ℝ m n) (β : Fin (cZ₁.h + cZ₂.h) → ℝ) : -- --- CONCL ---
    (cZ₁.conIntersect cZ₂ M).c
        + ∑ j : Fin (cZ₁.conIntersect cZ₂ M).h, β j • (cZ₁.conIntersect cZ₂ M).G j
      = cZ₁.c + ∑ j, β (Fin.castAdd cZ₂.h j) • cZ₁.G j := by -- --- PROOF ---
  show cZ₁.c + ∑ j : Fin (cZ₁.h + cZ₂.h), β j • (cZ₁.conIntersect cZ₂ M).G j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.conIntersect, Fin.append_left, Fin.append_right, Pi.zero_apply,
    smul_zero, Finset.sum_const_zero, add_zero]

/-- Coordinate `i` of the image of a point of `cZ₁`. -/
theorem ConZonotope.aux_image_coord (cZ : ConZonotope (Vec ℝ n)) (M : Mat ℝ m n)
    (β : Fin cZ.h → ℝ) (i : Fin m) :
    (M *ᵥ (cZ.c + ∑ j, β j • cZ.G j)) i
      = (M *ᵥ cZ.c) i + ∑ j, (M *ᵥ cZ.G j) i * β j := by
  rw [Matrix.mulVec_add, Matrix.mulVec_sum, Pi.add_apply, Finset.sum_apply]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.conIntersect_exact (cZ₁ : ConZonotope (Vec ℝ n)) (cZ₂ : ConZonotope (Vec ℝ m))
    (M : Mat ℝ m n) : -- --- CONCL ---
    {x | x ∈ cZ₁.construct ∧ M *ᵥ x ∈ cZ₂.construct}
      = (cZ₁.conIntersect cZ₂ M).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨β₁, hβ₁, hP₁, hx₁⟩, β₂, hβ₂, hP₂, hx₂⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_, ?_⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    -- the appended coefficient meets both polytopes, and the image rows read the two points
    · refine (ConZonotope.aux_mem_conIntersect_P_iff cZ₁ cZ₂ M _).mpr ⟨⟨?_, ?_⟩, fun i => ?_⟩
      · rw [blockLeft_append]; exact hP₁
      · rw [blockRight_append]; exact hP₂
      · have s₁ : (∑ j, (M *ᵥ cZ₁.G j) i * Fin.append β₁ β₂ (Fin.castAdd cZ₂.h j))
            = ∑ j, (M *ᵥ cZ₁.G j) i * β₁ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
        have s₂ : (∑ j, cZ₂.G j i * Fin.append β₁ β₂ (Fin.natAdd cZ₁.h j))
            = ∑ j, cZ₂.G j i * β₂ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]
        have e₁ := ConZonotope.aux_image_coord cZ₁ M β₁ i
        have e₂ : (M *ᵥ x) i = cZ₂.c i + ∑ j, cZ₂.G j i * β₂ j := by
          rw [hx₂, Entrywise.add_sum_smul_apply]
        rw [← hx₁] at e₁
        rw [s₁, s₂]
        linarith
    · have hs : (∑ j, Fin.append β₁ β₂ (Fin.castAdd cZ₂.h j) • cZ₁.G j) = ∑ j, β₁ j • cZ₁.G j :=
        Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
      rw [ConZonotope.aux_value_conIntersect, hs]
      exact hx₁
  -- back: the two halves of `β` are the two sets' own coefficients
  · rintro x ⟨β, hβ, hP, hx⟩
    obtain ⟨⟨hP₁, hP₂⟩, hagree⟩ := (ConZonotope.aux_mem_conIntersect_P_iff cZ₁ cZ₂ M β).mp hP
    have hx₁ : x = cZ₁.c + ∑ j, β (Fin.castAdd cZ₂.h j) • cZ₁.G j := by
      rw [hx, ConZonotope.aux_value_conIntersect]
    refine ⟨⟨fun j => β (Fin.castAdd cZ₂.h j), fun j => hβ _, hP₁, hx₁⟩,
      fun j => β (Fin.natAdd cZ₁.h j), fun j => hβ _, hP₂, ?_⟩
    funext i
    rw [Entrywise.add_sum_smul_apply]
    have e₁ := ConZonotope.aux_image_coord cZ₁ M (fun j => β (Fin.castAdd cZ₂.h j)) i
    rw [← hx₁] at e₁
    have hg := hagree i
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
