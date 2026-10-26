module

public import CORALean.Specification.FourValued.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Operations.Until
public import CORALean.Specification.FourValuedSignal.Operations.UntilFloat
public import CORALean.Specification.FourValuedSignal.Theorems.MinMaxSpec
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalMapTime
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UntilSpec
public import CORALean.Specification.KleeneSignal.Theorems.CombineMapTime
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalOptionMapTime
public import CORALean.Specification.KleeneSignal.Theorems.UntilFloatSound

@[expose] public section

/-!
# A float until of four-valued signals is sound

Read as reals, `untilFloat` is `True` at a time `t ≥ 0` only where the until of the signals read
as reals is `True`, and `False` only where that is `False`: a conclusive float value has its two
Kleene untils agree on it, and each of them is sound (`KleeneSignal.untilFloat_sound`), so the
exact Kleene untils agree on it too. `Unknown` and `Inconclusive` claim nothing.

## Inputs
* `lhs` – left signal
* `rhs` – right signal
* `U` – time interval

## Hypotheses
* `hl` – the left signal read as reals is valid
* `hr` – the right signal read as reals is valid

## Conclusion
* a float `True` or `False` is the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.untilFloat_sound (lhs rhs : FourValuedSignal 𝕋)
    (hl : (lhs.mapTime toReal).IsValid) (hr : (rhs.mapTime toReal).IsValid)
    (U : STLInterval 𝕋) : -- --- CONCL ---
    ∀ rf ∈ lhs.untilFloat U rhs, ∀ re ∈ (lhs.mapTime toReal).until U.toRealInterval
      (rhs.mapTime toReal), ∀ t : ℝ, 0 ≤ t →
      ((rf.mapTime toReal).at t = FourValued.tt → re.at t = FourValued.tt) ∧
      ((rf.mapTime toReal).at t = FourValued.ff → re.at t = FourValued.ff) := by -- --- PROOF ---
  intro rf hrf re hre t ht
  -- the refinements read as reals are valid
  have hlf := (FourValuedSignal.toKleeneSignal_spec _ hl Kleene.ff).1
  have hrf' := (FourValuedSignal.toKleeneSignal_spec _ hr Kleene.ff).1
  have hlt := (FourValuedSignal.toKleeneSignal_spec _ hl Kleene.tt).1
  have hrt := (FourValuedSignal.toKleeneSignal_spec _ hr Kleene.tt).1
  rw [← FourValuedSignal.toKleeneSignal_mapTime] at hlf hlt
  rw [← FourValuedSignal.toKleeneSignal_mapTime] at hrf' hrt
  -- the two float Kleene untils, read as reals, are valid and sound
  obtain ⟨hvmn, hmn⟩ := KleeneSignal.untilFloat_sound _ _ hlf hrf' U
  obtain ⟨hvmx, hmx⟩ := KleeneSignal.untilFloat_sound _ _ hlt hrt U
  simp only [FourValuedSignal.toKleeneSignal_mapTime] at hmn hmx
  -- the float result read as reals is the pair of the minimal until and its disagreement
  simp only [FourValuedSignal.untilFloat, Option.mem_def, Option.map_eq_some_iff] at hrf
  obtain ⟨inc, hinc, rfl⟩ := hrf
  set mn := (lhs.toKleeneSignal Kleene.ff).untilFloat U (rhs.toKleeneSignal Kleene.ff) with hmnd
  set mx := (lhs.toKleeneSignal Kleene.tt).untilFloat U (rhs.toKleeneSignal Kleene.tt) with hmxd
  have hK : (KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
      Kleene.fromBool (decide (args 0 ≠ args 1))) ![mn, mx] ()).mapTime toReal =
      KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
        Kleene.fromBool (decide (args 0 ≠ args 1))) ![mn.mapTime toReal, mx.mapTime toReal] () := by
    rw [KleeneSignal.combine_mapTime]; congr 1; funext k; fin_cases k <;> rfl
  obtain ⟨inc', hinc', -, hF⟩ := FourValuedSignal.minMax_spec _ _ _ hvmn hvmx hK
  rw [KleeneSignal.toBoolSignal?_mapTime, hinc, Option.map_some, Option.some.injEq] at hinc'
  subst hinc'
  obtain ⟨hFi, hFe⟩ := hF t ht
  -- the exact result agrees with its two Kleene untils where they agree
  obtain ⟨r, hr', -, hE⟩ := FourValuedSignal.until_spec _ _ hl hr U.toRealInterval
  obtain rfl : r = re := Option.some.inj (hr'.symm.trans hre)
  obtain ⟨-, hEe, -, -⟩ := hE t ht
  -- a conclusive float value has the two float untils agree on it
  have hagree : ∀ v : FourValued, v ≠ FourValued.ii →
      (FourValuedSignal.mapTime toReal ⟨mn, inc⟩).at t = v →
      FourValued.fromKleene ((mn.mapTime toReal).at t) = v ∧
        (mn.mapTime toReal).at t = (mx.mapTime toReal).at t := fun v hv h => by
    have heq := not_not.1 (mt hFi.2 (by rw [show FourValuedSignal.mapTime toReal ⟨_, inc⟩ =
      ⟨_, inc.mapTime toReal⟩ from rfl] at h; rw [h]; exact hv))
    refine ⟨?_, heq⟩
    rw [← hFe heq]
    exact h
  -- `True`: both float untils `True`, so both exact ones, and the exact result with them
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hagree _ (fun e => FourValued.noConfusion e) h
    rw [FourValued.fromKleene_eq_tt_iff] at h1
    have e1 := (hmn t ht).1 h1
    have e2 := (hmx t ht).1 (h2 ▸ h1)
    rw [hEe (e1.trans e2.symm), e1]
    rfl
  -- `False` likewise
  · intro h
    obtain ⟨h1, h2⟩ := hagree _ (fun e => FourValued.noConfusion e) h
    rw [FourValued.fromKleene_eq_ff_iff] at h1
    have e1 := (hmn t ht).2 h1
    have e2 := (hmx t ht).2 (h2 ▸ h1)
    rw [hEe (e1.trans e2.symm), e1]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
