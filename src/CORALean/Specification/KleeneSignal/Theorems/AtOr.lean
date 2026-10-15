module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.Or
public import CORALean.Specification.KleeneSignal.Theorems.MinMaxSpec
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalAtIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineSpec

@[expose] public section

/-!
# The disjunction of three-valued signals

For valid three-valued signals, `or_(varargin)` is valid and, at a time `t ≥ 0`, `True` iff one is
`True`, and `False` iff every one is `False`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The disjunction of Kleene signals is Kleene's disjunction. -/
theorem KleeneSignal.at_or {ι : Type} [Fintype ι] [Nonempty ι]
    (sigs : ι → KleeneSignal ℝ) (hv : ∀ k, (sigs k).IsValid) :
    (KleeneSignal.or_ sigs).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((KleeneSignal.or_ sigs).at t = Kleene.tt ↔ ∃ k, (sigs k).at t = Kleene.tt) ∧
      ((KleeneSignal.or_ sigs).at t = Kleene.ff ↔
        ∀ k, (sigs k).at t = Kleene.ff) := by -- --- PROOF ---
  -- the minimal and maximal refinements are valid
  have hvmn : ∀ k, ((sigs k).toBoolSignal false).IsValid :=
    fun k => (KleeneSignal.toBoolSignal_spec _ (hv k) false).1
  have hvmx : ∀ k, ((sigs k).toBoolSignal true).IsValid :=
    fun k => (KleeneSignal.toBoolSignal_spec _ (hv k) true).1
  obtain ⟨hvm, hm⟩ := PointSegmentSignal.combine_spec
    (fun (args : ι → Bool) (_ : Unit) => decide (∃ k, args k = true)) _ hvmn ()
  obtain ⟨hvx, hx⟩ := PointSegmentSignal.combine_spec
    (fun (args : ι → Bool) (_ : Unit) => decide (∃ k, args k = true)) _ hvmx ()
  obtain ⟨hv', h⟩ := KleeneSignal.minMax_spec _ _ hvm hvx
  refine ⟨hv', fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  rw [hm t ht, hx t ht] at h1 h2
  -- the refinements are read by `toBoolSignal_at_iff`
  have hat := fun k => KleeneSignal.toBoolSignal_at_iff _ (hv k) t ht
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, (hat _).1, (hat _).2] at h1 h2
  constructor
  · refine h1.trans ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by simp [hk]⟩
  · refine h2.trans ?_
    constructor
    · rintro ⟨hn1, hn2⟩ k
      by_contra hne
      exact hn2 ⟨k, hne⟩
    · intro hall
      exact ⟨fun ⟨k, hk⟩ => by simp [hall k] at hk, fun ⟨k, hk⟩ => hk (hall k)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
