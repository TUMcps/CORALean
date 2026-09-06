import CORALean.ContSet.ConZonotope.Real.Operations.And
import CORALean.ContSet.ConZonotope.Real.Operations.AgreeMat
import CORALean.ContSet.HPolytope.Real.Operations.MemEqsIff
import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact

/-!
# `ConZonotope.and` is exactly the intersection

Each block keeps its own polytope, which `plus` already decomposes, so only the
agreement rows add anything: they say the two points agree coordinate by
coordinate, which is what membership in both means.

Exact, and this is the whole case for constrained zonotopes — a zonotope
intersected with a zonotope is not a zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The agreement rows are all that `and` adds over `plus`. -/
theorem ConZonotope.aux_mem_and_P_iff (C₁ C₂ : ConZonotope (Vec ℝ n))
    (β : Vec ℝ (C₁.and C₂).h) :
    β ∈ (C₁.and C₂).P.construct ↔
      (blockLeft C₁.h C₂.h β ∈ C₁.P.construct
        ∧ blockRight C₁.h C₂.h β ∈ C₂.P.construct)
      ∧ ∀ i, (ConZonotope.agreeMat C₁ C₂ *ᵥ β) i = C₂.c i - C₁.c i := by
  -- via `mp`/`mpr`, not rewrites: writing the polytopes out needs an instance at an unreduced count
  constructor
  · intro h
    obtain ⟨hblocks, heqs⟩ := HPolytope.mem_and_iff.mp h
    exact ⟨HPolytope.mem_and_iff.mp hblocks, HPolytope.mem_eqs_iff.mp heqs⟩
  · rintro ⟨hblocks, heqs⟩
    exact HPolytope.mem_and_iff.mpr
      ⟨HPolytope.mem_and_iff.mpr hblocks, HPolytope.mem_eqs_iff.mpr heqs⟩

theorem ConZonotope.aux_mulVec_agree (C₁ C₂ : ConZonotope (Vec ℝ n))
    (β : Fin (C₁.h + C₂.h) → ℝ) (i : Fin n) :
    (ConZonotope.agreeMat C₁ C₂ *ᵥ β) i
      = (∑ j, C₁.G j i * β (Fin.castAdd C₂.h j))
        - ∑ j, C₂.G j i * β (Fin.natAdd C₁.h j) := by
  show ∑ j : Fin (C₁.h + C₂.h), ConZonotope.agreeMat C₁ C₂ i j * β j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.agreeMat, Fin.append_left, Fin.append_right, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- Only the first generator block survives; the second is pinned to it. -/
theorem ConZonotope.aux_value_and (C₁ C₂ : ConZonotope (Vec ℝ n))
    (β : Fin (C₁.h + C₂.h) → ℝ) :
    (C₁.and C₂).c + ∑ j : Fin (C₁.and C₂).h, β j • (C₁.and C₂).G j
      = C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j := by
  show (C₁.and C₂).c + ∑ j : Fin (C₁.h + C₂.h), β j • (C₁.and C₂).G j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.and, Fin.append_left, Fin.append_right, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, add_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.and_exact (C₁ C₂ : ConZonotope (Vec ℝ n)) :
    C₁.construct ∩ C₂.construct = (C₁.and C₂).construct := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨β₁, hβ₁, hP₁, hx₁⟩, β₂, hβ₂, hP₂, hx₂⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_, ?_⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    -- the appended coefficient meets both polytopes, and the agreement rows read the two points
    · refine (ConZonotope.aux_mem_and_P_iff C₁ C₂ _).mpr ⟨⟨?_, ?_⟩, fun i => ?_⟩
      · rw [blockLeft_append]; exact hP₁
      · rw [blockRight_append]; exact hP₂
      · have s₁ : (∑ j, C₁.G j i * Fin.append β₁ β₂ (Fin.castAdd C₂.h j))
            = ∑ j, C₁.G j i * β₁ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
        have s₂ : (∑ j, C₂.G j i * Fin.append β₁ β₂ (Fin.natAdd C₁.h j))
            = ∑ j, C₂.G j i * β₂ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]
        have e₁ : x i = C₁.c i + ∑ j, C₁.G j i * β₁ j := by
          rw [hx₁, Entrywise.add_sum_smul_apply]
        have e₂ : x i = C₂.c i + ∑ j, C₂.G j i * β₂ j := by
          rw [hx₂, Entrywise.add_sum_smul_apply]
        rw [ConZonotope.aux_mulVec_agree, s₁, s₂]
        linarith
    · have hs : (∑ j, Fin.append β₁ β₂ (Fin.castAdd C₂.h j) • C₁.G j) = ∑ j, β₁ j • C₁.G j :=
        Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
      rw [ConZonotope.aux_value_and, hs]
      exact hx₁
  -- back: the two halves of `β` are the two sets' own coefficients
  · rintro x ⟨β, hβ, hP, hx⟩
    obtain ⟨⟨hP₁, hP₂⟩, hagree⟩ := (ConZonotope.aux_mem_and_P_iff C₁ C₂ β).mp hP
    have hx₁ : x = C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j := by
      rw [hx, ConZonotope.aux_value_and]
    refine ⟨⟨fun j => β (Fin.castAdd C₂.h j), fun j => hβ _, hP₁, hx₁⟩,
      fun j => β (Fin.natAdd C₁.h j), fun j => hβ _, hP₂, ?_⟩
    funext i
    rw [Entrywise.add_sum_smul_apply]
    have e₁ : x i = C₁.c i + ∑ j, C₁.G j i * β (Fin.castAdd C₂.h j) := by
      rw [hx₁, Entrywise.add_sum_smul_apply]
    have hg := hagree i
    rw [ConZonotope.aux_mulVec_agree] at hg
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
