module

public import CORALean.Specification.FourValued.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Until
public import CORALean.Specification.FourValuedSignal.Theorems.MinMaxSpec
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAtIff
public import CORALean.Specification.KleeneSignal.Theorems.UntilSpec
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

@[expose] public section

/-!
# The until of four-valued signals

For valid four-valued signals over `ℝ` and an until interval with lower bound `≥ 0`,
`until(lhs,interval,rhs)` does not throw and is valid. At a time `t ≥ 0` it is inconclusive iff the
untils of the two Kleene refinements (inconclusive as `False`, as `True`) differ, and their common
value otherwise; it is `True` iff some `t'` with `t' - t` in the interval has the right-hand side
`True` and the left-hand side `True` strictly between, and `False` iff at every such `t'` the
right-hand side is `False` or the left-hand side is `False` somewhere strictly between.

The `True` and `False` clauses are the direct semantics of `U_I` on four-valued signals that
[1, Sec. 4.3 (operators)] describes by the pattern of [1, Eq. 2].

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The until of four-valued signals is inconclusive where the refinements differ. -/
theorem FourValuedSignal.until_spec (lhs rhs : FourValuedSignal ℝ) (hl : lhs.IsValid)
    (hr : rhs.IsValid) (U : STLInterval) : -- --- CONCL ---
    let minU := (lhs.toKleeneSignal Kleene.ff).until U (rhs.toKleeneSignal Kleene.ff)
    let maxU := (lhs.toKleeneSignal Kleene.tt).until U (rhs.toKleeneSignal Kleene.tt)
    ∃ r, lhs.until U rhs = some r ∧ r.IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (r.at t = FourValued.ii ↔ minU.at t ≠ maxU.at t) ∧
      (minU.at t = maxU.at t → r.at t = FourValued.fromKleene (minU.at t)) ∧
      (r.at t = FourValued.tt ↔ ∃ t', t' - t ∈ U.set ∧ rhs.at t' = FourValued.tt ∧
        ∀ x, t < x → x < t' → lhs.at x = FourValued.tt) ∧
      (r.at t = FourValued.ff ↔ ∀ t', t' - t ∈ U.set → rhs.at t' = FourValued.ff ∨
        ∃ x, t < x ∧ x < t' ∧ lhs.at x = FourValued.ff) := by -- --- PROOF ---
  intro minU maxU
  -- the refinements are valid, and so are their untils
  obtain ⟨hvm, hm⟩ := KleeneSignal.until_spec _ _ (lhs.toKleeneSignal_spec hl Kleene.ff).1
    (rhs.toKleeneSignal_spec hr Kleene.ff).1 U
  obtain ⟨hvx, hx⟩ := KleeneSignal.until_spec _ _ (lhs.toKleeneSignal_spec hl Kleene.tt).1
    (rhs.toKleeneSignal_spec hr Kleene.tt).1 U
  obtain ⟨inc, hinc, hvr, hmm⟩ := FourValuedSignal.minMax_spec _ _ _ hvm hvx rfl
  refine ⟨⟨_, inc⟩, ?_, hvr, fun t ht => ?_⟩
  · unfold FourValuedSignal.until
    dsimp only
    rw [hinc]
    rfl
  obtain ⟨hr1, hr2⟩ := hmm t ht
  obtain ⟨hmt, hmf⟩ := hm t ht
  obtain ⟨hxt, hxf⟩ := hx t ht
  -- a witness `t'` lies after `t`, so the refinements are read there
  have hpos : ∀ t', t' - t ∈ U.set → 0 ≤ t' := fun t' hu => by
    have := STLInterval.zero_le_of_mem_set U _ hu; linarith
  have hat := fun x (hx0 : 0 ≤ x) => lhs.toKleeneSignal_at_iff hl x hx0
  have hat' := fun x (hx0 : 0 ≤ x) => rhs.toKleeneSignal_at_iff hr x hx0
  -- the four conditions on the refinements, in terms of the four-valued signals
  have e1 : minU.at t =
      Kleene.tt ↔ ∃ t', t' - t ∈ U.set ∧ rhs.at t' = FourValued.tt ∧
        ∀ x, t < x → x < t' → lhs.at x = FourValued.tt :=
    hmt.trans (exists_congr fun t' => and_congr_right fun hu => and_congr
      (hat' t' (hpos t' hu)).1 (forall_congr' fun x => forall_congr' fun h1 =>
        forall_congr' fun h2 => (hat x (by linarith)).1))
  -- the same for the refinement with inconclusive as `True`
  have e3 : maxU.at t =
      Kleene.tt ↔ ∃ t', t' - t ∈ U.set ∧ (rhs.at t' = FourValued.tt ∨ rhs.at t' = FourValued.ii) ∧
        ∀ x, t < x → x < t' → lhs.at x = FourValued.tt ∨ lhs.at x = FourValued.ii :=
    hxt.trans (exists_congr fun t' => and_congr_right fun hu => and_congr
      (hat' t' (hpos t' hu)).2.2.2.1 (forall_congr' fun x => forall_congr' fun h1 =>
        forall_congr' fun h2 => (hat x (by linarith)).2.2.2.1))
  -- and the `False` conditions of the two refinements
  have e2 : minU.at t =
      Kleene.ff ↔ ∀ t', t' - t ∈ U.set → (rhs.at t' = FourValued.ff ∨ rhs.at t' = FourValued.ii) ∨
        ∃ x, t < x ∧ x < t' ∧ (lhs.at x = FourValued.ff ∨ lhs.at x = FourValued.ii) :=
    hmf.trans (forall_congr' fun t' => forall_congr' fun hu => or_congr (hat' t' (hpos t' hu)).2.1
      (exists_congr fun x => and_congr_right fun h1 => and_congr_right fun h2 =>
        (hat x (by linarith)).2.1))
  have e4 : maxU.at t =
      Kleene.ff ↔ ∀ t', t' - t ∈ U.set → rhs.at t' = FourValued.ff ∨
        ∃ x, t < x ∧ x < t' ∧ lhs.at x = FourValued.ff :=
    hxf.trans (forall_congr' fun t' => forall_congr' fun hu => or_congr
      (hat' t' (hpos t' hu)).2.2.2.2.1 (exists_congr fun x => and_congr_right fun h1 =>
        and_congr_right fun h2 => (hat x (by linarith)).2.2.2.2.1))
  -- the common value of the two refinements decides the result
  set a := minU.at t with ha
  set b := maxU.at t with hb
  refine ⟨hr1, hr2, ?_, ?_⟩
  · -- True: the two refinements agree and are True
    constructor
    · intro h
      have hab : a = b := by
        by_contra hne
        rw [hr1.2 hne] at h
        exact absurd h (by simp)
      rw [hr2 hab] at h
      exact e1.1 ((FourValued.fromKleene_eq_tt_iff a).1 h)
    · intro h
      have hat : a = Kleene.tt := e1.2 h
      have hbt : b = Kleene.tt := e3.2 (by
        obtain ⟨t', hu, hr', hl'⟩ := h
        exact ⟨t', hu, Or.inl hr', fun x h1 h2 => Or.inl (hl' x h1 h2)⟩)
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
      have haf : a = Kleene.ff := e2.2 (fun t' hu => by
        rcases h t' hu with h' | ⟨x, h1, h2, h3⟩
        · exact Or.inl (Or.inl h')
        · exact Or.inr ⟨x, h1, h2, Or.inl h3⟩)
      rw [hr2 (haf.trans hbf.symm), haf]
      rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
