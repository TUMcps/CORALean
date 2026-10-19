module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Theorems.CombineSpec
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalEqSome
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# A four-valued signal from its minimal and maximal refinements

`until`, `and_` and `or_` of `fourValuedSignal` build their result from the Kleene signals `mn`, the
operation on the refinements with inconclusive mapped to `False`, and `mx`, with it mapped to
`True`: the Kleene part is `mn`, and the value is inconclusive where they differ. For valid `mn`,
`mx`, the conversion `toBoolSignal()` of the difference succeeds, the signal is valid, inconclusive
exactly where `mn` and `mx` differ and `mn`'s value elsewhere.

`mn` and `mx` are `⌊Λ̃⌋` and `⌈Λ̃⌉` of the result, which is their `⊔₂`, as
[1, Sec. 4.3 (refinements)] recovers `Λ̃(t)`.

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

/-- The signal built from `mn` and `mx` is inconclusive where they differ. -/
theorem FourValuedSignal.minMax_spec (mn mx K : KleeneSignal ℝ) (hmn : mn.IsValid)
    (hmx : mx.IsValid) (hK : K = KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
      Kleene.fromBool (decide (args 0 ≠ args 1))) ![mn, mx] ()) : -- --- CONCL ---
    ∃ inc, K.toBoolSignal? = some inc ∧
    (⟨mn, inc⟩ : FourValuedSignal ℝ).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((⟨mn, inc⟩ : FourValuedSignal ℝ).at t = FourValued.ii ↔ mn.at t ≠ mx.at t) ∧
      (mn.at t = mx.at t → (⟨mn, inc⟩ : FourValuedSignal ℝ).at t = FourValued.fromKleene (mn.at t))
      := by -- --- PROOF ---
  -- the difference of the refinements, as a three-valued signal
  obtain ⟨hv, h⟩ := KleeneSignal.combine_spec
    (fun (args : Fin 2 → Kleene) (_ : Unit) => Kleene.fromBool (decide (args 0 ≠ args 1)))
    ![mn, mx] (Fin.forall_fin_two.2 ⟨hmn, hmx⟩) ()
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← hK] at hv h
  -- it is nowhere unknown, so `toBoolSignal` returns its Boolean part
  have hnu : ∀ t : ℝ, 0 ≤ t → K.at t ≠ Kleene.uu := fun t ht hu => by
    rw [h t ht] at hu
    by_cases hd : mn.at t = mx.at t <;> simp [Kleene.fromBool, hd] at hu
  have hsome := KleeneSignal.toBoolSignal?_eq_some _ hv hnu
  refine ⟨_, hsome, ⟨hmn, hv.1⟩, fun t ht => ?_⟩
  -- the Boolean part of the difference says where `mn` and `mx` differ
  have hk : K.signal.at t = decide (mn.at t ≠ mx.at t) := by
    have hat := h t ht
    have hun := (KleeneSignal.at_eq_uu_iff K t).not.1 (hnu t ht)
    simp only [KleeneSignal.at, Bool.not_eq_true] at hat hun
    rw [hun, if_neg (by simp)] at hat
    exact Kleene.fromBool_inj _ _ hat
  simp only [FourValuedSignal.at, hk]
  have hfi : ∀ k, FourValued.fromKleene k ≠ FourValued.ii := fun k => by
    cases k <;> simp [FourValued.fromKleene]
  by_cases hd : mn.at t = mx.at t
  · simp [hd, hfi]
  · simp [hd]
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
