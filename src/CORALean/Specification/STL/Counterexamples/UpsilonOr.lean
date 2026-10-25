module

public import CORALean.Specification.STL.Definitions.Transformation
public import CORALean.Specification.STL.Definitions.Tsupp
public import CORALean.Specification.STL.Theorems.SatOr
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Eq. 12 fails: `tsupp(ϕ)` need not decide `ϕ`

[1, Eq. 12] says a sound and complete `Υ` has `Υ(ϕ₁ ∨ ϕ₂) ≡ Υ(ϕ₁) ∨ Υ(ϕ₂)` if `tsupp(ϕ₁) ∩
tsupp(ϕ₂) = ∅`. Over `Bool`, with the atom `p` = `ξ(0) = true`, take `ϕ₂ = F(0,1) ¬p`
(`tsupp ⊆ (0,1)`) and `ϕ₁ = ¬X₁(p ∨ F(0,1) p) ∧ G(0,1) F(0,1) p` (true points of `(0,1)` cofinal,
so `tsupp(ϕ₁) ⊆ [1,2)`): the supports are disjoint, but `ϕ₁` depends on `(0,1)`. For the reach
sequence `R` that is `Bool` on `(0,1)` and `{false}` elsewhere, `C(R) ⊨ₜ ϕ₁ ∨ ϕ₂` while neither
holds of all of `C(R)`, so the equivalence fails for the `Υ` that is `A ⊤` or `A ⊥` as `C(R) ⊨ₜ ϕ`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the encoding of a disjunction is not the disjunction of the encodings

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The atom `ξ(0) = true`. -/
def STL.aux_p : STL.Formula Bool := .atom fun b => b = true

/-- `ϕ₂ = F(0,1) ¬p`. -/
def STL.aux_phi2 : STL.Formula Bool := .finOpen 1 (.not STL.aux_p)

/-- `ϕ₁ = ¬X₁(p ∨ F(0,1) p) ∧ G(0,1) F(0,1) p`. -/
def STL.aux_phi1 : STL.Formula Bool :=
  .and (.not (.next 1 (.or STL.aux_p (.finOpen 1 STL.aux_p))))
    (.globOpen 1 (.finOpen 1 STL.aux_p))

theorem STL.aux_phi2_sat (ξ : ℝ≥0 → Bool) :
    STL.aux_phi2.Satisfies ξ ↔ ∃ t, 0 < t ∧ t < 1 ∧ ξ t = false := by
  simp [STL.aux_phi2, STL.aux_p, STL.Formula.Satisfies, Time.shift]

theorem STL.aux_phi1_sat (ξ : ℝ≥0 → Bool) : -- --- CONCL ---
    STL.aux_phi1.Satisfies ξ ↔ (ξ 1 = false ∧ ∀ s, 0 < s → s < 1 → ξ (s + 1) = false) ∧
      ∀ t, 0 < t → t < 1 → ∃ u, t < u ∧ u < 1 + t ∧ ξ u = true := by -- --- PROOF ---
  -- the window `(0,1)` after `t` is the interval `(t, 1 + t)` of points `u = s + t`
  have key : ∀ t : ℝ≥0, (∃ s, 0 < s ∧ s < 1 ∧ ξ (s + t) = true) ↔
      ∃ u, t < u ∧ u < 1 + t ∧ ξ u = true := fun t => by
    constructor
    · rintro ⟨s, h0, h1, h⟩
      exact ⟨s + t, lt_add_of_pos_left _ h0, (add_lt_add_iff_right t).2 h1, h⟩
    · rintro ⟨u, h0, h1, h⟩
      -- the window offset is `s = u - t`
      refine ⟨u - t, tsub_pos_of_lt h0, ?_, by rwa [tsub_add_cancel_of_le h0.le]⟩
      exact (tsub_lt_iff_left h0.le).2 (by rwa [add_comm] at h1)
  simp only [STL.aux_phi1, STL.aux_p, STL.Formula.and, STL.Formula.next, STL.Formula.tt,
    STL.Formula.Satisfies, Time.shift, zero_add, not_exists, not_and, not_or, not_not, not_forall]
  -- the guard is the first conjunct, the cofinality the second, with `u = s + t`
  refine and_congr ?_ (forall₃_congr fun t _ _ => by
    -- each direction swaps the order of the two bounds
    rw [← key t]
    constructor <;> rintro ⟨a, b, c, d⟩ <;> first | exact ⟨a, c, b, d⟩ | exact ⟨a, b, c, d⟩)
  -- the guard: both of its points are false
  constructor
  · intro h
    -- the `until` of the guard is at time `1` only
    refine ⟨?_, fun s hs0 hs1 => ?_⟩
    · cases hx : ξ 1
      · rfl
      · obtain ⟨_, _, hh⟩ := h 1 le_rfl le_rfl (Or.inl hx)
        exact absurd trivial hh
    · cases hx : ξ (s + 1)
      · rfl
      · obtain ⟨_, _, hh⟩ := h 1 le_rfl le_rfl (Or.inr ⟨s, hs0, hs1, hx⟩)
        exact absurd trivial hh
  · rintro ⟨h1, h2⟩ x hx1 hx2 (hP | ⟨t, ht0, ht1, ht⟩)
    · have : x = 1 := le_antisymm hx2 hx1
      subst this
      simp [h1] at hP
    · have : x = 1 := le_antisymm hx2 hx1
      subst this
      simp [h2 t ht0 ht1] at ht

theorem STL.aux_one_add_lt_two {a : ℝ≥0} (ha : a < 1) : 1 + a < 2 :=
  calc 1 + a < 1 + 1 := (add_lt_add_iff_left 1).2 ha
    _ = 2 := one_add_one_eq_two

/-- Changing one point outside `[1,2)` keeps `ϕ₁` true. -/
theorem STL.aux_phi1_sat_of_ne {t : ℝ≥0} (ht : t < 1 ∨ 2 ≤ t) {ξ ξ' : ℝ≥0 → Bool}
    (hag : ∀ t', t' ≠ t → ξ t' = ξ' t') (h : STL.aux_phi1.Satisfies ξ) : -- --- CONCL ---
    STL.aux_phi1.Satisfies ξ' := by -- --- PROOF ---
  rw [STL.aux_phi1_sat] at h ⊢
  obtain ⟨⟨hz1, hz⟩, hc⟩ := h
  -- the guard on `[1,2)` is unchanged, since `t` is not in it
  have hne1 : (1 : ℝ≥0) ≠ t := by
    rintro rfl
    rcases ht with h | h
    · exact lt_irrefl _ h
    · exact absurd h (by norm_num)
  refine ⟨⟨by rw [← hag 1 hne1, hz1], fun s h0 h1 => ?_⟩, fun t' h0 h1 => ?_⟩
  · have : s + 1 ≠ t := by
      rintro rfl
      rcases ht with h | h
      · exact absurd h (not_lt.2 le_add_self)
      · have := STL.aux_one_add_lt_two h1
        rw [add_comm] at this
        exact absurd h (not_le.2 this)
    rw [← hag _ this, hz s h0 h1]
  -- the cofinality: a witness at `max t' t` is not the changed point `t`
  · rcases ht with ht | ht
    -- a witness for `max t' t`, which lies below `1` by the guard
    · set m := max t' t with hm
      have hm1 : m < 1 := max_lt h1 ht
      have hm0 : 0 < m := lt_max_of_lt_left h0
      obtain ⟨u, hu1, hu2, hu3⟩ := hc m hm0 hm1
      -- the witness lies below `1`, else it is in the guard, where `ξ` is false
      have hu : u < 1 := by
        by_contra hu
        rw [not_lt] at hu
        rcases hu.eq_or_lt with rfl | hlt
        · simp [hz1] at hu3
        · have h0' : 0 < u - 1 := tsub_pos_of_lt hlt
          have h2 : 1 + m < 2 := STL.aux_one_add_lt_two hm1
          have h1' : u - 1 < 1 :=
            (tsub_lt_iff_left hu).2 ((hu2.trans h2).trans_eq one_add_one_eq_two.symm)
          have := hz (u - 1) h0' h1'
          rw [tsub_add_cancel_of_le hu] at this
          simp [this] at hu3
      refine ⟨u, lt_of_le_of_lt (le_max_left _ _) hu1, hu.trans_le le_self_add, ?_⟩
      rw [← hag u (ne_of_gt (lt_of_le_of_lt (le_max_right _ _) hu1)), hu3]
    · obtain ⟨u, hu1, hu2, hu3⟩ := hc t' h0 h1
      have : u < 2 := hu2.trans (STL.aux_one_add_lt_two h1)
      have hne : u ≠ t := ne_of_lt (this.trans_le ht)
      exact ⟨u, hu1, hu2, by rw [← hag u hne, hu3]⟩

/-- `tsupp(ϕ₁) ⊆ [1,2)`. -/
theorem STL.aux_phi1_tsupp_subset {t : ℝ≥0} (h : t ∈ STL.aux_phi1.tsupp) : -- --- CONCL ---
    1 ≤ t ∧ t < 2 := by -- --- PROOF ---
  by_contra hnot
  have ht : t < 1 ∨ 2 ≤ t := by
    rw [not_and_or, not_le, not_lt] at hnot
    exact hnot
  obtain ⟨ξ, ξ', hs, hn, hag⟩ := h
  exact hn (STL.aux_phi1_sat_of_ne ht hag hs)

/-- `tsupp(ϕ₂) ⊆ (0,1)`. -/
theorem STL.aux_phi2_tsupp_subset {t : ℝ≥0} (h : t ∈ STL.aux_phi2.tsupp) : -- --- CONCL ---
    0 < t ∧ t < 1 := by -- --- PROOF ---
  by_contra hnot
  obtain ⟨ξ, ξ', hs, hn, hag⟩ := h
  rw [STL.aux_phi2_sat] at hs hn
  obtain ⟨s, h0, h1, hs⟩ := hs
  refine hn ⟨s, h0, h1, ?_⟩
  rw [← hag s (fun hst => hnot (hst ▸ ⟨h0, h1⟩)), hs]

/-- `tsupp(ϕ₁)` and `tsupp(ϕ₂)` are disjoint. -/
theorem STL.aux_cexTsupp_disjoint : Disjoint STL.aux_phi1.tsupp STL.aux_phi2.tsupp :=
  Set.disjoint_left.2 fun _ h1 h2 =>
    absurd (STL.aux_phi2_tsupp_subset h2).2 (not_lt.2 (STL.aux_phi1_tsupp_subset h1).1)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 12] fails: `ϕ₁`, `ϕ₂` with disjoint `tsupp` and a sound and complete `Υ` with
`Υ(ϕ₁ ∨ ϕ₂) ≢ Υ(ϕ₁) ∨ Υ(ϕ₂)`. -/
theorem STL.upsilon_or_counterexample : -- --- CONCL ---
    ∃ (R : ℝ≥0 → Set Bool) (Υ : STL.Formula Bool → RTL.Formula Bool) (φ₁ φ₂ : STL.Formula Bool),
      STL.IsSound {R} Υ ∧ STL.IsComplete {R} Υ ∧ Disjoint φ₁.tsupp φ₂.tsupp ∧
        ¬ ((Υ (φ₁.or φ₂)).Satisfies R ↔ (RTL.Formula.or (Υ φ₁) (Υ φ₂)).Satisfies
        R) := by -- --- PROOF ---
  classical
  let R : ℝ≥0 → Set Bool := fun t => if 0 < t ∧ t < 1 then Set.univ else {false}
  let Υ : STL.Formula Bool → RTL.Formula Bool := fun φ =>
    if φ.HoldsOn (ReachSequence.traceSet R) then .A Pform.top else .A Pform.bot
  have h0 : R 0 = {false} := by simp [R]
  have hbot : ¬ (RTL.Formula.A Pform.bot).Satisfies R := fun h => h false (by simp [h0])
  have htop : (RTL.Formula.A Pform.top).Satisfies R := fun r _ => trivial
  -- the values off `(0,1)` are `false`
  have hR1 : ∀ ξ ∈ ReachSequence.traceSet R, ∀ t, ¬ (0 < t ∧ t < 1) → ξ t = false :=
      fun ξ hξ t ht => by
    have := hξ t
    simpa [R, ht] using this
  -- `C(R) ⊨ₜ ϕ₁ ∨ ϕ₂`
  have hval : (STL.aux_phi1.or STL.aux_phi2).HoldsOn (ReachSequence.traceSet R) := by
    intro ξ hξ
    by_cases h2 : ∃ t, 0 < t ∧ t < 1 ∧ ξ t = false
    · exact (STL.Formula.sat_or _ _ _).2 (Or.inr ((STL.aux_phi2_sat ξ).2 h2))
    refine (STL.Formula.sat_or _ _ _).2
      (Or.inl ((STL.aux_phi1_sat ξ).2 ⟨⟨?_, fun s hs0 hs1 => ?_⟩, ?_⟩))
    · exact hR1 ξ hξ 1 (by simp)
    · exact hR1 ξ hξ _ (fun h => absurd h.2 (not_lt.2 le_add_self))
    · intro t ht0 ht1
      have ht1' : (t : ℝ) < 1 := by exact_mod_cast ht1
      have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
      have hu1 : t < (t + 1) / 2 := by
        rw [← NNReal.coe_lt_coe]; push_cast; linarith
      have hu2 : (t + 1) / 2 < 1 := by
        rw [← NNReal.coe_lt_coe]; push_cast; linarith
      have hu3 : (t + 1) / 2 < 1 + t := by
        rw [← NNReal.coe_lt_coe]; push_cast; linarith
      refine ⟨(t + 1) / 2, hu1, hu3, ?_⟩
      by_contra hne
      exact h2 ⟨(t + 1) / 2, hu1.trans' ht0, hu2, by simpa using hne⟩
  -- `ϕ₁` fails on the all-false trace, whose true set is empty
  have hn1 : ¬ STL.aux_phi1.HoldsOn (ReachSequence.traceSet R) := by
    intro h
    have hξ : (fun _ => false : ℝ≥0 → Bool) ∈ ReachSequence.traceSet R := fun t => by
      by_cases ht : 0 < t ∧ t < 1 <;> simp [R, ht]
    have := (STL.aux_phi1_sat _).1 (h _ hξ)
    obtain ⟨u, _, _, hu⟩ := this.2 (1 / 2) (by norm_num) (by norm_num)
    simp at hu
  have hn2 : ¬ STL.aux_phi2.HoldsOn (ReachSequence.traceSet R) := by
    intro h
    have hξ : (fun t => if 0 < t ∧ t < 1 then true else false : ℝ≥0 → Bool) ∈
        ReachSequence.traceSet R := fun t => by
      by_cases ht : 0 < t ∧ t < 1 <;> simp [R, ht]
    obtain ⟨t, ht0, ht1, ht⟩ := (STL.aux_phi2_sat _).1 (h _ hξ)
    simp [ht0, ht1] at ht
  -- `Υ` is sound and complete for `{R}`, and the equivalence fails
  refine ⟨R, Υ, STL.aux_phi1, STL.aux_phi2, ?_, ?_, STL.aux_cexTsupp_disjoint, ?_⟩
  · rintro R' rfl φ h
    by_contra hφ
    exact hbot (by simpa [Υ, hφ] using h)
  · rintro R' rfl φ h
    have : Υ φ = RTL.Formula.A Pform.top := if_pos h
    rw [this]; exact htop
  · intro h
    have e0 : Υ (STL.aux_phi1.or STL.aux_phi2) = RTL.Formula.A Pform.top := if_pos hval
    have e1 : Υ STL.aux_phi1 = RTL.Formula.A Pform.bot := if_neg hn1
    have e2 : Υ STL.aux_phi2 = RTL.Formula.A Pform.bot := if_neg hn2
    have := h.1 (by rw [e0]; exact htop)
    rw [e1, e2] at this
    rcases this with h' | h' <;> exact hbot h'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
