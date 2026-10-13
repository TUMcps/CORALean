module

public import CORALean.Specification.STL.Definitions.ReachSequence
public import CORALean.Specification.STL.Theorems.PformSatBigOr
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `F(0,c)` and `G(0,c)` on an open block, as a condition on its set

The core of [1, Lemma 2], Eq. (17): on a block `(a, a + c)` where `R` is the constant `S`, every
trace in `C(R)` satisfies `⋁_k F(0,c)ϱ_k ∨ ⋁_l G(0,c)ϱ_l` iff `S` satisfies `ϱ' = ⋁_k ϱ_k`, or
`ϱ_l ∨ ϱ'` for some `l`. The paper proves it for three disjuncts; the converse builds a trace that
visits, for each `l`, a state refuting `ϱ_l ∨ ϱ'` at its own time `c / (l + 2)`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSequence.forall_finals_or_globals_iff {R : ℝ≥0 → Set X}
    (hne : ∀ t, (R t).Nonempty) {a c : ℝ≥0} (hc : 0 < c) {S : Set X}
    (hS : ∀ x, a < x → x < a + c → R x = S) (K L : List (Pform X)) :
    (∀ ξ ∈ ReachSequence.traceSet R,
      (∃ ϱ ∈ K, ∃ t, 0 < t ∧ t < c ∧ ϱ.Sat (ξ (t + a))) ∨
        ∃ ϱ ∈ L, ∀ t, 0 < t → t < c → ϱ.Sat (ξ (t + a))) ↔
      (∀ r ∈ S, (Pform.bigOr K).Sat r) ∨
        ∃ ϱ ∈ L, ∀ r ∈ S, (Pform.or ϱ (Pform.bigOr K)).Sat r := by -- --- PROOF ---
  classical
  -- inside the block, `R` is `S`
  have hSt : ∀ t, 0 < t → t < c → R (t + a) = S := fun t h₀ h₁ =>
    hS _ (lt_add_of_pos_left a h₀) (by rw [add_comm a c]; exact add_lt_add_of_lt_of_le h₁ le_rfl)
  constructor
  · intro hL
    by_contra hR
    push Not at hR
    obtain ⟨⟨r₀, hr₀S, hr₀⟩, hR₂⟩ := hR
    -- for each `l` a state of `S` refuting `ϱ_l ∨ ϱ'`
    choose g hgS hg using fun i : Fin L.length => hR₂ L[i] (List.getElem_mem i.2)
    -- the times `c / (i + 2)` lie in `(0, c)` and are pairwise distinct
    let τ : Fin L.length → ℝ≥0 := fun i => c / ((i : ℕ) + 2)
    have hτ₀ : ∀ i, 0 < τ i := fun i => div_pos hc (by positivity)
    have hτ₁ : ∀ i, τ i < c := fun i => div_lt_self hc (lt_of_lt_of_le one_lt_two le_add_self)
    have hτi : ∀ i j, τ i = τ j → i = j := by
      intro i j h
      have := (div_eq_div_iff (by positivity) (by positivity)).1 h
      have := mul_left_cancel₀ hc.ne' this
      exact Fin.ext (by exact_mod_cast (add_right_cancel (by exact_mod_cast this.symm)))
    -- the trace: `g i` at time `τ i + a`, `r₀` elsewhere in the block, anything outside
    let ξ : ℝ≥0 → X := fun x =>
      if h : ∃ i, x = τ i + a then g h.choose
      else if a < x ∧ x < a + c then r₀ else (hne x).some
    have hmid : ∀ i, a < τ i + a ∧ τ i + a < a + c := fun i =>
      ⟨lt_add_of_pos_left a (hτ₀ i), by
        rw [add_comm a c]; exact add_lt_add_of_lt_of_le (hτ₁ i) le_rfl⟩
    have hξ : ξ ∈ ReachSequence.traceSet R := by
      intro x
      by_cases h : ∃ i, x = τ i + a
      · have hxR : R x = S := by rw [h.choose_spec]; exact hSt _ (hτ₀ _) (hτ₁ _)
        simp only [ξ, dif_pos h]
        rw [hxR]; exact hgS _
      · by_cases hx : a < x ∧ x < a + c
        · simp only [ξ, dif_neg h, if_pos hx]
          rw [hS x hx.1 hx.2]; exact hr₀S
        · simpa only [ξ, dif_neg h, if_neg hx] using (hne x).some_mem
    -- `ϱ'` fails at every state this trace visits in the block
    rcases hL ξ hξ with ⟨ϱ, hϱK, t, ht₀, ht₁, hsat⟩ | ⟨ϱ, hϱL, hall⟩
    · by_cases h : ∃ i, t + a = τ i + a
      · have e : ξ (t + a) = g h.choose := by simp only [ξ, dif_pos h]
        rw [e] at hsat
        exact hg h.choose (Or.inr ((Pform.sat_bigOr K _).2 ⟨ϱ, hϱK, hsat⟩))
      · have hx : a < t + a ∧ t + a < a + c :=
          ⟨lt_add_of_pos_left a ht₀, by rw [add_comm a c]; exact add_lt_add_of_lt_of_le ht₁ le_rfl⟩
        have e : ξ (t + a) = r₀ := by simp only [ξ, dif_neg h, if_pos hx]
        rw [e] at hsat
        exact hr₀ ((Pform.sat_bigOr K _).2 ⟨ϱ, hϱK, hsat⟩)
    · -- `ϱ_l = L[i]` fails at its own time `τ i + a`
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hϱL
      have hh : ∃ j, τ ⟨i, hi⟩ + a = τ j + a := ⟨_, rfl⟩
      have e : ξ (τ ⟨i, hi⟩ + a) = g ⟨i, hi⟩ := by
        simp only [ξ, dif_pos hh]
        congr 1
        exact (hτi _ _ (add_right_cancel hh.choose_spec)).symm
      have := hall (τ ⟨i, hi⟩) (hτ₀ _) (hτ₁ _)
      rw [e] at this
      exact hg ⟨i, hi⟩ (Or.inl this)
  · intro hR ξ hξ
    have hxS : ∀ t, 0 < t → t < c → ξ (t + a) ∈ S := fun t h₀ h₁ => by
      rw [← hSt t h₀ h₁]; exact hξ _
    rcases hR with hall | ⟨ϱ, hϱL, hall⟩
    · -- `ϱ'` holds of every state of `S`, so of the trace at the midpoint
      obtain ⟨ϱ, hϱ, hs⟩ :=
        (Pform.sat_bigOr K _).1 (hall _ (hxS (c / 2) (half_pos hc) (half_lt_self hc)))
      exact Or.inl ⟨ϱ, hϱ, c / 2, half_pos hc, half_lt_self hc, hs⟩
    · by_cases hF : ∃ ϱ ∈ K, ∃ t, 0 < t ∧ t < c ∧ ϱ.Sat (ξ (t + a))
      · exact Or.inl hF
      · -- no `ϱ_k` ever holds, so `ϱ_l` holds throughout
        refine Or.inr ⟨ϱ, hϱL, fun t h₀ h₁ => ?_⟩
        rcases hall _ (hxS t h₀ h₁) with h | h
        · exact h
        · obtain ⟨ϱk, hk, hs⟩ := (Pform.sat_bigOr K _).1 h
          exact absurd ⟨ϱk, hk, t, h₀, h₁, hs⟩ hF

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
