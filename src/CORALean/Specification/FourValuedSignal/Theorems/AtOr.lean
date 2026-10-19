module

public import CORALean.Specification.FourValued.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Or
public import CORALean.Specification.FourValuedSignal.Theorems.MinMaxSpec
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAtIff
public import CORALean.Specification.Kleene.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.AtAnd
public import CORALean.Specification.KleeneSignal.Theorems.AtOr

@[expose] public section

/-!
# The disjunction of four-valued signals

For valid four-valued signals, `fourValuedSignal.or_(varargin)` does not throw, is valid and, at a
time `t ≥ 0`, `True` iff one signal is `True`, `False` iff every one is `False`, and `Inconclusive`
iff none is `True` and one is `Inconclusive`; otherwise `Unknown`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The disjunction of four-valued signals is `True`, `False`, `Inconclusive` as `fourValued.or`. -/
theorem FourValuedSignal.at_or {ι : Type} [Fintype ι] [Nonempty ι] (sigs : ι → FourValuedSignal ℝ)
    (hv : ∀ k, (sigs k).IsValid) : -- --- CONCL ---
    ∃ r, FourValuedSignal.or_ sigs = some r ∧ r.IsValid ∧
      ∀ t : ℝ, 0 ≤ t → (r.at t = FourValued.tt ↔ ∃ k, (sigs k).at t = FourValued.tt) ∧
        (r.at t = FourValued.ff ↔ ∀ k, (sigs k).at t = FourValued.ff) ∧
        (r.at t = FourValued.ii ↔
          (∀ k, (sigs k).at t ≠ FourValued.tt) ∧
            ∃ k, (sigs k).at t = FourValued.ii) := by -- --- PROOF ---
  -- the refinements are valid, and so are their disjunctions
  obtain ⟨hvm, hm⟩ := KleeneSignal.at_or (fun k => (sigs k).toKleeneSignal Kleene.ff)
    (fun k => ((sigs k).toKleeneSignal_spec (hv k) Kleene.ff).1)
  obtain ⟨hvx, hx⟩ := KleeneSignal.at_or (fun k => (sigs k).toKleeneSignal Kleene.tt)
    (fun k => ((sigs k).toKleeneSignal_spec (hv k) Kleene.tt).1)
  obtain ⟨inc, hinc, hvr, hr⟩ := FourValuedSignal.minMax_spec _ _ _ hvm hvx rfl
  refine ⟨⟨_, inc⟩, ?_, hvr, fun t ht => ?_⟩
  · unfold FourValuedSignal.or_
    dsimp only
    rw [hinc]
    rfl
  -- the two refinements, read off at each signal
  obtain ⟨hr1, hr2⟩ := hr t ht
  have hk := fun k => (sigs k).toKleeneSignal_at_iff (hv k) t ht
  have e1 : (KleeneSignal.or_ fun k => (sigs k).toKleeneSignal Kleene.ff).at t = Kleene.tt ↔
      ∃ k, (sigs k).at t = FourValued.tt :=
    (hm t ht).1.trans (exists_congr fun k => (hk k).1)
  have e2 : (KleeneSignal.or_ fun k => (sigs k).toKleeneSignal Kleene.ff).at t = Kleene.ff ↔
      ∀ k, (sigs k).at t = FourValued.ff ∨ (sigs k).at t = FourValued.ii :=
    (hm t ht).2.trans (forall_congr' fun k => (hk k).2.1)
  have e3 : (KleeneSignal.or_ fun k => (sigs k).toKleeneSignal Kleene.tt).at t = Kleene.tt ↔
      ∃ k, (sigs k).at t = FourValued.tt ∨ (sigs k).at t = FourValued.ii :=
    (hx t ht).1.trans (exists_congr fun k => (hk k).2.2.2.1)
  have e4 : (KleeneSignal.or_ fun k => (sigs k).toKleeneSignal Kleene.tt).at t = Kleene.ff ↔
      ∀ k, (sigs k).at t = FourValued.ff :=
    (hx t ht).2.trans (forall_congr' fun k => (hk k).2.2.2.2.1)
  set a := (KleeneSignal.or_ fun k => (sigs k).toKleeneSignal Kleene.ff).at t with ha
  set b := (KleeneSignal.or_ fun k => (sigs k).toKleeneSignal Kleene.tt).at t with hb
  refine ⟨?_, ?_, ?_⟩
  · -- True: the two refinements agree and are True
    constructor
    · intro h
      have hab : a = b := by
        by_contra hne
        rw [hr1.2 hne] at h
        exact absurd h (by simp)
      rw [hr2 hab] at h
      exact e1.1 ((FourValued.fromKleene_eq_tt_iff a).1 h)
    · rintro ⟨k, hk'⟩
      have hat : a = Kleene.tt := e1.2 ⟨k, hk'⟩
      have hbt : b = Kleene.tt := e3.2 ⟨k, Or.inl hk'⟩
      rw [hr2 (hat.trans hbt.symm), hat]
      rfl
  · -- False: the two refinements agree and are False
    constructor
    · intro h
      have hab : a = b := by
        by_contra hne
        rw [hr1.2 hne] at h
        exact absurd h (by simp)
      rw [hr2 hab] at h
      exact e4.1 (hab ▸ (FourValued.fromKleene_eq_ff_iff a).1 h)
    · intro h
      have hbf : b = Kleene.ff := e4.2 h
      have haf : a = Kleene.ff := e2.2 fun k => Or.inl (h k)
      rw [hr2 (haf.trans hbf.symm), haf]
      rfl
  · -- Inconclusive: they differ
    rw [hr1]
    constructor
    · intro hne
      -- no signal is True, else both refinements are True
      have hnt : ∀ k, (sigs k).at t ≠ FourValued.tt := fun k hk =>
        hne ((e1.2 ⟨k, hk⟩).trans (e3.2 ⟨k, Or.inl hk⟩).symm)
      refine ⟨hnt, ?_⟩
      by_contra hno
      have hno' : ∀ k, (sigs k).at t ≠ FourValued.ii := fun k hk => hno ⟨k, hk⟩
      refine hne (Kleene.eq_of_ff_iff a b ?_ ?_ ?_)
      · exact ⟨fun h => e4.2 fun k => (e2.1 h k).resolve_right (hno' k), fun h =>
          e2.2 fun k => Or.inl (e4.1 h k)⟩
      · intro hat
        obtain ⟨k, hk⟩ := e1.1 hat
        exact hnt k hk
      · intro hbt
        obtain ⟨k, hk | hk⟩ := e3.1 hbt
        · exact hnt k hk
        · exact hno' k hk
    · rintro ⟨hnt, k, hk⟩ hab
      obtain ⟨j, hj⟩ := e1.1 (hab ▸ e3.2 ⟨k, Or.inr hk⟩)
      exact hnt j hj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
