module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `ConZonotope.intersection` is exactly the intersection

Each block keeps its own polytope, which `plus` already decomposes, so only the
agreement rows add anything: they say the two points agree coordinate by
coordinate, which is what membership in both means.

Exact [1, Prop. 1], and this is the whole case for constrained zonotopes — a zonotope
intersected with a zonotope is not a zonotope.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Hypotheses
* none

## Conclusion
* the result is exactly the intersection

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The agreement rows are all that `intersection` adds over `plus`. -/
theorem ConZonotope.aux_mem_intersection_P_iff (cZ₁ cZ₂ : ConZonotope (Vec ℝ n))
    (β : Vec ℝ (cZ₁.intersection cZ₂).h) : -- --- CONCL ---
    β ∈ (cZ₁.intersection cZ₂).P.construct ↔
      (blockLeft cZ₁.h cZ₂.h β ∈ cZ₁.P.construct
        ∧ blockRight cZ₁.h cZ₂.h β ∈ cZ₂.P.construct)
      ∧ ∀ i, (ConZonotope.aux_agreeMat cZ₁ cZ₂ *ᵥ β) i = cZ₂.c i - cZ₁.c i := by -- --- PROOF ---
  -- via `mp`/`mpr`, not rewrites: writing the polytopes out needs an instance at an unreduced count
  constructor
  · intro h
    obtain ⟨hblocks, heqs⟩ := HPolytope.mem_intersection_iff.mp h
    exact ⟨HPolytope.mem_intersection_iff.mp hblocks, HPolytope.mem_eqs_iff.mp heqs⟩
  · rintro ⟨hblocks, heqs⟩
    exact HPolytope.mem_intersection_iff.mpr
      ⟨HPolytope.mem_intersection_iff.mpr hblocks, HPolytope.mem_eqs_iff.mpr heqs⟩

theorem ConZonotope.aux_mulVec_agree (cZ₁ cZ₂ : ConZonotope (Vec ℝ n))
    (β : Fin (cZ₁.h + cZ₂.h) → ℝ) (i : Fin n) : -- --- CONCL ---
    (ConZonotope.aux_agreeMat cZ₁ cZ₂ *ᵥ β) i
      = (∑ j, cZ₁.G j i * β (Fin.castAdd cZ₂.h j))
        - ∑ j, cZ₂.G j i * β (Fin.natAdd cZ₁.h j) := by -- --- PROOF ---
  show ∑ j : Fin (cZ₁.h + cZ₂.h), ConZonotope.aux_agreeMat cZ₁ cZ₂ i j * β j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.aux_agreeMat, Fin.append_left, Fin.append_right, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- Only the first generator block survives; the second is pinned to it. -/
theorem ConZonotope.aux_value_intersection (cZ₁ cZ₂ : ConZonotope (Vec ℝ n))
    (β : Fin (cZ₁.h + cZ₂.h) → ℝ) :
    (cZ₁.intersection cZ₂).c + ∑ j : Fin (cZ₁.intersection cZ₂).h, β j • (cZ₁.intersection cZ₂).G j
      = cZ₁.c + ∑ j, β (Fin.castAdd cZ₂.h j) • cZ₁.G j := by
  show (cZ₁.intersection cZ₂).c + ∑ j : Fin (cZ₁.h + cZ₂.h), β j • (cZ₁.intersection cZ₂).G j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.intersection, Fin.append_left, Fin.append_right, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, add_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intersection_exact (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) : -- --- CONCL ---
    cZ₁.construct ∩ cZ₂.construct = (cZ₁.intersection cZ₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨β₁, hβ₁, hP₁, hx₁⟩, β₂, hβ₂, hP₂, hx₂⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_, ?_⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    -- the appended coefficient meets both polytopes, and the agreement rows read the two points
    · refine (ConZonotope.aux_mem_intersection_P_iff cZ₁ cZ₂ _).mpr ⟨⟨?_, ?_⟩, fun i => ?_⟩
      · rw [blockLeft_append]; exact hP₁
      · rw [blockRight_append]; exact hP₂
      · have s₁ : (∑ j, cZ₁.G j i * Fin.append β₁ β₂ (Fin.castAdd cZ₂.h j))
            = ∑ j, cZ₁.G j i * β₁ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
        have s₂ : (∑ j, cZ₂.G j i * Fin.append β₁ β₂ (Fin.natAdd cZ₁.h j))
            = ∑ j, cZ₂.G j i * β₂ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]
        have e₁ : x i = cZ₁.c i + ∑ j, cZ₁.G j i * β₁ j := by
          rw [hx₁, Entrywise.add_sum_smul_apply]
        have e₂ : x i = cZ₂.c i + ∑ j, cZ₂.G j i * β₂ j := by
          rw [hx₂, Entrywise.add_sum_smul_apply]
        rw [ConZonotope.aux_mulVec_agree, s₁, s₂]
        linarith
    · have hs : (∑ j, Fin.append β₁ β₂ (Fin.castAdd cZ₂.h j) • cZ₁.G j) = ∑ j, β₁ j • cZ₁.G j :=
        Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
      rw [ConZonotope.aux_value_intersection, hs]
      exact hx₁
  -- back: the two halves of `β` are the two sets' own coefficients
  · rintro x ⟨β, hβ, hP, hx⟩
    obtain ⟨⟨hP₁, hP₂⟩, hagree⟩ := (ConZonotope.aux_mem_intersection_P_iff cZ₁ cZ₂ β).mp hP
    have hx₁ : x = cZ₁.c + ∑ j, β (Fin.castAdd cZ₂.h j) • cZ₁.G j := by
      rw [hx, ConZonotope.aux_value_intersection]
    refine ⟨⟨fun j => β (Fin.castAdd cZ₂.h j), fun j => hβ _, hP₁, hx₁⟩,
      fun j => β (Fin.natAdd cZ₁.h j), fun j => hβ _, hP₂, ?_⟩
    funext i
    rw [Entrywise.add_sum_smul_apply]
    have e₁ : x i = cZ₁.c i + ∑ j, cZ₁.G j i * β (Fin.castAdd cZ₂.h j) := by
      rw [hx₁, Entrywise.add_sum_smul_apply]
    have hg := hagree i
    rw [ConZonotope.aux_mulVec_agree] at hg
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
