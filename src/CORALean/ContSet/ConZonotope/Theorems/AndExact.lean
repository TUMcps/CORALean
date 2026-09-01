import CORALean.ContSet.ConZonotope.Operations.And
import CORALean.ContSet.ConZonotope.Theorems.PlusExact

/-!
# `ConZonotope.and` is exactly the intersection

The first `q₁ + q₂` rows are the block-diagonal system `plus` already
decomposes, so only the last `n` add anything: they say the two points agree
coordinate by coordinate, which is what membership in both means.

Exact, and this is the whole case for constrained zonotopes — a zonotope
intersected with a zonotope is not a zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- A point of a zonotope read coordinatewise, which is the form the agreement
rows are stated in. -/
theorem ConZonotope.aux_coord {m : ℕ} (c : Vec ℝ n) (G : Fin m → Vec ℝ n) (β : Fin m → ℝ)
    (i : Fin n) : (c + ∑ j, β j • G j) i = c i + ∑ j, G j i * β j := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)

theorem ConZonotope.aux_and_A_left (C₁ C₂ : ConZonotope (Vec ℝ n)) (i : Fin (C₁.q + C₂.q)) :
    (C₁.and C₂).A (Fin.castAdd n i) = (C₁.plus C₂).A i := by
  simp only [ConZonotope.and, ConZonotope.plus, Fin.append_left]

theorem ConZonotope.aux_and_b_left (C₁ C₂ : ConZonotope (Vec ℝ n)) (i : Fin (C₁.q + C₂.q)) :
    (C₁.and C₂).b (Fin.castAdd n i) = (C₁.plus C₂).b i := by
  simp only [ConZonotope.and, ConZonotope.plus, Fin.append_left]

theorem ConZonotope.aux_and_b_right (C₁ C₂ : ConZonotope (Vec ℝ n)) (i : Fin n) :
    (C₁.and C₂).b (Fin.natAdd (C₁.q + C₂.q) i) = C₂.c i - C₁.c i := by
  simp only [ConZonotope.and, Fin.append_right]

theorem ConZonotope.aux_mulVec_and_left (C₁ C₂ : ConZonotope (Vec ℝ n))
    (β : Fin (C₁.h + C₂.h) → ℝ) (i : Fin (C₁.q + C₂.q)) :
    ((C₁.and C₂).A *ᵥ β) (Fin.castAdd n i) = ((C₁.plus C₂).A *ᵥ β) i := by
  show ∑ j : Fin (C₁.h + C₂.h), (C₁.and C₂).A (Fin.castAdd n i) j * β j
    = ∑ j : Fin (C₁.h + C₂.h), (C₁.plus C₂).A i j * β j
  rw [ConZonotope.aux_and_A_left]

theorem ConZonotope.aux_mulVec_and_right (C₁ C₂ : ConZonotope (Vec ℝ n))
    (β : Fin (C₁.h + C₂.h) → ℝ) (i : Fin n) :
    ((C₁.and C₂).A *ᵥ β) (Fin.natAdd (C₁.q + C₂.q) i)
      = (∑ j, C₁.G j i * β (Fin.castAdd C₂.h j))
        - ∑ j, C₂.G j i * β (Fin.natAdd C₁.h j) := by
  show ∑ j : Fin (C₁.h + C₂.h), (C₁.and C₂).A (Fin.natAdd (C₁.q + C₂.q) i) j * β j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.and, Fin.append_left, Fin.append_right, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- The last `n` rows are all that `and` adds over `plus`. -/
theorem ConZonotope.aux_constraint_and (C₁ C₂ : ConZonotope (Vec ℝ n))
    (β : Fin (C₁.h + C₂.h) → ℝ) :
    (C₁.and C₂).A *ᵥ β = (C₁.and C₂).b
      ↔ ((C₁.A *ᵥ fun j => β (Fin.castAdd C₂.h j)) = C₁.b
          ∧ (C₂.A *ᵥ fun j => β (Fin.natAdd C₁.h j)) = C₂.b)
        ∧ ∀ i, (∑ j, C₁.G j i * β (Fin.castAdd C₂.h j))
            - (∑ j, C₂.G j i * β (Fin.natAdd C₁.h j)) = C₂.c i - C₁.c i := by
  rw [← ConZonotope.aux_constraint_plus]
  constructor
  · intro hall
    constructor
    · funext i
      rw [← ConZonotope.aux_mulVec_and_left, ← ConZonotope.aux_and_b_left, hall]
    · intro i
      rw [← ConZonotope.aux_mulVec_and_right, ← ConZonotope.aux_and_b_right, hall]
  · rintro ⟨hplus, hagree⟩
    refine funext (Fin.addCases (fun i => ?_) fun i => ?_)
    · rw [ConZonotope.aux_mulVec_and_left, ConZonotope.aux_and_b_left, hplus]
    · rw [ConZonotope.aux_mulVec_and_right, ConZonotope.aux_and_b_right, hagree]

/-- Only the first generator block survives; the second is pinned to it. -/
theorem ConZonotope.aux_value_and (C₁ C₂ : ConZonotope (Vec ℝ n))
    (β : Fin (C₁.h + C₂.h) → ℝ) :
    (C₁.and C₂).c + ∑ j : Fin (C₁.and C₂).h, β j • (C₁.and C₂).G j
      = C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j := by
  show (C₁.and C₂).c + ∑ j : Fin (C₁.h + C₂.h), β j • (C₁.and C₂).G j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.and, Fin.append_left, Fin.append_right, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, add_zero]

theorem ConZonotope.and_exact (C₁ C₂ : ConZonotope (Vec ℝ n)) :
    C₁.construct ∩ C₂.construct = (C₁.and C₂).construct := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨β₁, hβ₁, hA₁, hx₁⟩, β₂, hβ₂, hA₂, hx₂⟩
    have happ₁ : (fun j => Fin.append β₁ β₂ (Fin.castAdd C₂.h j)) = β₁ :=
      funext fun j => Fin.append_left β₁ β₂ j
    have happ₂ : (fun j => Fin.append β₁ β₂ (Fin.natAdd C₁.h j)) = β₂ :=
      funext fun j => Fin.append_right β₁ β₂ j
    refine ⟨Fin.append β₁ β₂, ?_, ?_, ?_⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    · refine (ConZonotope.aux_constraint_and C₁ C₂ _).mpr ⟨⟨?_, ?_⟩, fun i => ?_⟩
      · rw [happ₁]; exact hA₁
      · rw [happ₂]; exact hA₂
      · have s₁ : (∑ j, C₁.G j i * Fin.append β₁ β₂ (Fin.castAdd C₂.h j))
            = ∑ j, C₁.G j i * β₁ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
        have s₂ : (∑ j, C₂.G j i * Fin.append β₁ β₂ (Fin.natAdd C₁.h j))
            = ∑ j, C₂.G j i * β₂ j :=
          Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]
        have e₁ : x i = C₁.c i + ∑ j, C₁.G j i * β₁ j := by
          rw [hx₁, ConZonotope.aux_coord]
        have e₂ : x i = C₂.c i + ∑ j, C₂.G j i * β₂ j := by
          rw [hx₂, ConZonotope.aux_coord]
        rw [s₁, s₂]
        linarith
    · have hs : (∑ j, Fin.append β₁ β₂ (Fin.castAdd C₂.h j) • C₁.G j) = ∑ j, β₁ j • C₁.G j :=
        Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
      rw [ConZonotope.aux_value_and, hs]
      exact hx₁
  · rintro x ⟨β, hβ, hA, hx⟩
    obtain ⟨⟨hA₁, hA₂⟩, hagree⟩ := (ConZonotope.aux_constraint_and C₁ C₂ β).mp hA
    have hx₁ : x = C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j := by
      rw [hx, ConZonotope.aux_value_and]
    refine ⟨⟨fun j => β (Fin.castAdd C₂.h j), fun j => hβ _, hA₁, hx₁⟩,
      fun j => β (Fin.natAdd C₁.h j), fun j => hβ _, hA₂, ?_⟩
    funext i
    rw [ConZonotope.aux_coord]
    have e₁ : x i = C₁.c i + ∑ j, C₁.G j i * β (Fin.castAdd C₂.h j) := by
      rw [hx₁, ConZonotope.aux_coord]
    linarith [hagree i]

end CORALean.Real
