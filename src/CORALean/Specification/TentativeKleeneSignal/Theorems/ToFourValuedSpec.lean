module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.NotAt
public import CORALean.Specification.PointSegmentSignal.Theorems.NotIsValid
public import CORALean.Specification.TentativeKleeneSignal.Definitions.IsValid
public import CORALean.Specification.TentativeKleeneSignal.Operations.ToFourValued

@[expose] public section

/-!
# The four-valued signal of a tentative signal

`toFourValued(obj)` of a valid signal is valid and has, at every `t ≥ 0`, the value the tentative
signal denotes: `Inconclusive` where neither value can hold, `Unknown` where both can, else the one
that can.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.toFourValued_spec (s : TentativeKleeneSignal ℝ) (hs : s.IsValid) :
    s.toFourValued.IsValid ∧ ∀ t : ℝ, 0 ≤ t → s.toFourValued.at t = s.at t := by -- --- PROOF ---
  have hv : ∀ k : Fin 2, (![s.canBeTrue, s.canBeFalse] k).IsValid :=
    Fin.forall_fin_two.2 ⟨hs.1, hs.2⟩
  obtain ⟨hv1, h1⟩ := PointSegmentSignal.combine_spec (fun (a : Fin 2 → Bool) (_ : Unit) =>
    (a 0 && a 1)) ![s.canBeTrue, s.canBeFalse] hv ()
  obtain ⟨hv2, h2⟩ := PointSegmentSignal.combine_spec (fun (a : Fin 2 → Bool) (_ : Unit) =>
    (a 0 || a 1)) ![s.canBeTrue, s.canBeFalse] hv ()
  refine ⟨⟨⟨hs.1, hv1⟩, PointSegmentSignal.not_isValid _ hv2⟩, fun t ht => ?_⟩
  have e1 := h1 t ht
  have e2 := h2 t ht
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
  simp only [FourValuedSignal.at, KleeneSignal.at, TentativeKleeneSignal.toFourValued,
    PointSegmentSignal.not_at _ hv2, e1, e2, TentativeKleeneSignal.at]
  rcases Bool.eq_false_or_eq_true (s.canBeTrue.at t) with hA | hA <;>
    rcases Bool.eq_false_or_eq_true (s.canBeFalse.at t) with hB | hB <;>
    simp [FourValued.fromKleene, Kleene.fromBool, hA, hB]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
