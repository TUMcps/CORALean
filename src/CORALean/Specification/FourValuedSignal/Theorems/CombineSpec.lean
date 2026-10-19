module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Theorems.CombineSpec
public import CORALean.Specification.KleeneSignal.Theorems.FromBoolSignalSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.AnyTrueEqFalseOfAt
public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# Point-wise combination of four-valued signals is point-wise

For valid inputs, each output of `combine(op,varargin)` is a valid signal whose value at every
time `t ≥ 0` is `op` applied to the four-valued values of the inputs at `t`. The unknown part of the
inconclusive output is `false` throughout, so `toBoolSignal()` does not throw; this uses a time
between any two points and one after the last (`DenselyOrdered`, `NoMaxOrder`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.combine_spec {ι κ : Type} [Fintype ι] [Nonempty ι] (op : (ι →
    FourValued) → κ → FourValued)
    (sig : ι → FourValuedSignal ℝ) (hv : ∀ k, (sig k).IsValid) (i : κ) : -- --- CONCL ---
    (FourValuedSignal.combine op sig i).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (FourValuedSignal.combine op sig i).at t = op (fun k => (sig k).at t) i := by -- --- PROOF ---
  unfold FourValuedSignal.combine
  generalize hc : Sum.elim (fun k => (sig k).signal)
    (fun k => KleeneSignal.fromBoolSignal (sig k).isInconclusive) = c
  generalize hk : (fun (args : ι ⊕ ι → Kleene) (o : κ × Bool) =>
    if o.2 then Kleene.fromBool (op (fun k => FourValued.ofKleeneInc (args (Sum.inl k))
      (args (Sum.inr k)).toBool) o.1).isInconclusive
    else (op (fun k => FourValued.ofKleeneInc (args (Sum.inl k))
      (args (Sum.inr k)).toBool) o.1).toKleene) = u2Op
  have hcv : ∀ x, (c x).IsValid := by
    rw [← hc]
    rintro (k | k)
    · exact (hv k).1
    · exact (KleeneSignal.fromBoolSignal_spec _ (hv k).2).1
  have hcat : ∀ t : ℝ, 0 ≤ t → ∀ k, (c (Sum.inl k)).at t = (sig k).signal.at t ∧
      (c (Sum.inr k)).at t = Kleene.fromBool ((sig k).isInconclusive.at t) := by
    intro t ht k
    rw [← hc]
    exact ⟨rfl, (KleeneSignal.fromBoolSignal_spec _ (hv k).2).2 t ht⟩
  have hsp := fun o => KleeneSignal.combine_spec u2Op c hcv o
  -- the joined inputs are the inputs' values
  have hkey : ∀ t : ℝ, 0 ≤ t →
      u2Op (fun x => (c x).at t) (i, false) = (op (fun k => (sig k).at t) i).toKleene ∧
      u2Op (fun x => (c x).at t) (i, true) =
        Kleene.fromBool (op (fun k => (sig k).at t) i).isInconclusive := by
    intro t ht
    have hu : (fun k => FourValued.ofKleeneInc ((fun x => (c x).at t) (Sum.inl k))
        ((fun x => (c x).at t) (Sum.inr k)).toBool) = fun k => (sig k).at t := by
      funext k
      simp only [(hcat t ht k).1, (hcat t ht k).2, FourValuedSignal.at]
      cases (sig k).isInconclusive.at t <;> rfl
    rw [← hk]
    constructor
    · simp only [hu, Bool.false_eq_true, if_false]
    · simp only [hu, if_true]
  obtain ⟨hvU, hatU⟩ := hsp (i, true)
  obtain ⟨hvS, hatS⟩ := hsp (i, false)
  -- the unknown part of the inconclusive output never holds
  have hunk : ∀ t : ℝ, 0 ≤ t → (KleeneSignal.combine u2Op c (i, true)).isUnknown.at t = false := by
    intro t ht
    by_contra hne
    have hu : (KleeneSignal.combine u2Op c (i, true)).isUnknown.at t = true := by simpa using hne
    have h1 := hatU t ht
    rw [(hkey t ht).2] at h1
    simp only [KleeneSignal.at, hu, if_true] at h1
    simp only [Kleene.fromBool] at h1
    split_ifs at h1
  have hany := PointSegmentSignal.anyTrue_eq_false_of_at _ hvU.2 hunk 0 ⊤ true false
  have hopt : (KleeneSignal.combine u2Op c (i, true)).toBoolSignal? =
      some (KleeneSignal.combine u2Op c (i, true)).signal := by
    simp [KleeneSignal.toBoolSignal?, hany]
  dsimp only
  -- so `toBoolSignal()` returns the Boolean part, and the output is the value `op` gives
  refine ⟨⟨hvS, by rw [hopt]; exact hvU.1⟩, fun t ht => ?_⟩
  generalize hr : op (fun k => (sig k).at t) i = r
  have h1 := hatU t ht
  rw [(hkey t ht).2, hr] at h1
  have h2 := hatS t ht
  rw [(hkey t ht).1, hr] at h2
  simp only [KleeneSignal.at, hunk t ht, Bool.false_eq_true, if_false] at h1
  simp only [FourValuedSignal.at, hopt, Option.getD_some]
  rw [h2]
  rw [Kleene.fromBool_inj _ _ h1]
  exact FourValued.ofKleeneInc_toKleene_isInconclusive r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
