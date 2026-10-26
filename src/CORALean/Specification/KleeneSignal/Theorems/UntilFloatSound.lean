module

public import CORALean.Specification.KleeneSignal.Operations.Until
public import CORALean.Specification.KleeneSignal.Operations.UntilFloat
public import CORALean.Specification.KleeneSignal.Theorems.MinMaxSpec
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalMapTime
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilFloatSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.UntilFloatInner
public import CORALean.Specification.PointSegmentSignal.Theorems.UntilFloatOuter
public import CORALean.Specification.PointSegmentSignal.Theorems.UntilMono
public import CORALean.Specification.PointSegmentSignal.Theorems.UntilSpec
public import CORALean.Specification.STLInterval.Theorems.SetMinusInwardInner
public import CORALean.Specification.STLInterval.Theorems.SetMinusOuter

@[expose] public section

/-!
# A float until of three-valued signals is sound

Read as reals, `untilFloat` is `True` at a time `t ≥ 0` only where the until of the signals read as
reals is `True`, and `False` only where that is `False`: its minimal refinement's until, shifted
inward, is true only where the exact one is (`untilFloat_inner`), and its maximal refinement's,
shifted outward, true wherever the exact one is (`untilFloat_outer`). An `Unknown` claims nothing.

## Inputs
* `lhs` – left signal
* `rhs` – right signal
* `U` – time interval

## Hypotheses
* `hl` – the left signal read as reals is valid
* `hr` – the right signal read as reals is valid

## Conclusion
* the float until read as reals is valid, and a float `True` or `False` is the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Mapping unknown to `false` gives a signal below mapping it to `true`. -/
private theorem KleeneSignal.aux_toBoolSignal_le (s : KleeneSignal ℝ)
    (hs : s.IsValid) : -- --- CONCL ---
    ∀ x : ℝ, 0 ≤ x →
      (s.toBoolSignal false).at x ≤ (s.toBoolSignal true).at x := by -- --- PROOF ---
  intro x hx
  obtain ⟨-, hf⟩ := KleeneSignal.toBoolSignal_spec s hs false
  obtain ⟨-, ht⟩ := KleeneSignal.toBoolSignal_spec s hs true
  by_cases hu : s.at x = Kleene.uu
  · rw [(hf x hx).1 hu, (ht x hx).1 hu]; exact Bool.false_le true
  · rw [(hf x hx).2 hu, (ht x hx).2 hu]


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.untilFloat_sound (lhs rhs : KleeneSignal 𝕋)
    (hl : (lhs.mapTime toReal).IsValid) (hr : (rhs.mapTime toReal).IsValid)
    (U : STLInterval 𝕋) : -- --- CONCL ---
    ((lhs.untilFloat U rhs).mapTime toReal).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (((lhs.untilFloat U rhs).mapTime toReal).at t = Kleene.tt →
        ((lhs.mapTime toReal).until U.toRealInterval (rhs.mapTime toReal)).at t = Kleene.tt) ∧
      (((lhs.untilFloat U rhs).mapTime toReal).at t = Kleene.ff →
        ((lhs.mapTime toReal).until U.toRealInterval (rhs.mapTime toReal)).at t =
          Kleene.ff) := by -- --- PROOF ---
  -- the float refinements' untils, read as reals
  set mnF := ((lhs.toBoolSignal false).untilFloat STLInterval.minusInward U
    (rhs.toBoolSignal false)).mapTime toReal with hmnF
  set mxF := ((lhs.toBoolSignal true).untilFloat STLInterval.minus U
    (rhs.toBoolSignal true)).mapTime toReal with hmxF
  have hF : (lhs.untilFloat U rhs).mapTime toReal = ⟨mnF, PointSegmentSignal.combine
      (fun (args : Fin 2 → Bool) (_ : Unit) => decide (args 0 ≠ args 1)) ![mnF, mxF] ()⟩ := by
    simp only [KleeneSignal.untilFloat, KleeneSignal.mapTime, PointSegmentSignal.combine_mapTime,
      hmnF, hmxF]
    congr 2
    funext k
    fin_cases k <;> rfl
  have hvmnF : mnF.IsValid :=
    (PointSegmentSignal.intervalUntilFloat_spec STLInterval.minusInward _ _ U).2.1
  have hvmxF : mxF.IsValid :=
    (PointSegmentSignal.intervalUntilFloat_spec STLInterval.minus _ _ U).2.1
  -- the exact refinements' untils
  have hlf := (KleeneSignal.toBoolSignal_spec _ hl false).1
  have hrf := (KleeneSignal.toBoolSignal_spec _ hr false).1
  have hlt := (KleeneSignal.toBoolSignal_spec _ hl true).1
  have hrt := (KleeneSignal.toBoolSignal_spec _ hr true).1
  have hvmnE := (PointSegmentSignal.until_spec _ _ hlf hrf U.toRealInterval).1
  have hvmxE := (PointSegmentSignal.until_spec _ _ hlt hrt U.toRealInterval).1
  obtain ⟨hvF, hFat⟩ := KleeneSignal.minMax_spec mnF mxF hvmnF hvmxF
  obtain ⟨-, hEat⟩ := KleeneSignal.minMax_spec _ _ hvmnE hvmxE
  rw [hF]
  refine ⟨hvF, fun t ht => ?_⟩
  -- the inner until is true only where the exact one is, the outer wherever it is
  have hin : mnF.at t = true → (((lhs.mapTime toReal).toBoolSignal false).until U.toRealInterval
      ((rhs.mapTime toReal).toBoolSignal false)).at t = true := by
    rw [← KleeneSignal.toBoolSignal_mapTime, ← KleeneSignal.toBoolSignal_mapTime]
    exact PointSegmentSignal.untilFloat_inner _ STLInterval.set_minusInward_inner _ _ U t ht
  have hout : (((lhs.mapTime toReal).toBoolSignal true).until U.toRealInterval
      ((rhs.mapTime toReal).toBoolSignal true)).at t = true → mxF.at t = true := by
    rw [← KleeneSignal.toBoolSignal_mapTime, ← KleeneSignal.toBoolSignal_mapTime]
    exact PointSegmentSignal.untilFloat_outer _ STLInterval.set_minus_outer _ _ U t ht
  -- the exact minimal until is below the maximal one
  have hmono := PointSegmentSignal.until_mono _ _ _ _ hlf hlt hrf hrt U.toRealInterval
    (KleeneSignal.aux_toBoolSignal_le _ hl) (KleeneSignal.aux_toBoolSignal_le _ hr) t ht
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- `True`: the minimal untils are true, so the exact maximal one is too
    have h1 := hin ((hFat t ht).1.1 h).1
    exact (hEat t ht).1.2 ⟨h1, Bool.le_iff_imp.1 hmono h1⟩
  · -- `False`: the maximal untils are false, so the exact minimal one is too
    have h2 : (((lhs.mapTime toReal).toBoolSignal true).until U.toRealInterval
        ((rhs.mapTime toReal).toBoolSignal true)).at t = false := by
      have := ((hFat t ht).2.1 h).2
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rw [hout hc] at this
      exact Bool.noConfusion this
    refine (hEat t ht).2.2 ⟨Bool.eq_false_iff.2 fun hc => ?_, h2⟩
    rw [Bool.le_iff_imp.1 hmono hc] at h2
    exact Bool.noConfusion h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
