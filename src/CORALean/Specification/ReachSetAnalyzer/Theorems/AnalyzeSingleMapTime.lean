module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Global.FoldlMOptionMap
public import CORALean.Global.LookupMapSnd
public import CORALean.Global.MapMOptionMap
public import CORALean.Global.ReplaceKeyMapSnd
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.CombineMapTime
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.FiniteSignal.Theorems.MaxSpec
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeSingle
public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.ReachSetAnalyzer.Theorems.MaskOkMapTime

public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.SetPossiblyFalseMapTime
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.SetPossiblyTrueMapTime
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeKey
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTimeInterval

@[expose] public section

/-!
# One reach set analyzed over float time stamps, read as reals

An analyzer over a float scalar `T` marks each proposition by comparing its time stamps exactly
(`TimeOrder`: the mask, the builders' indicators and combinations), so analyzing one reach set,
read through `toReal`, is analyzing the reach set read as reals, and both throw together.

## Inputs
* `obj` – analyzer
* `R` – reach set entry

## Hypotheses
* none

## Conclusion
* the float result, read as reals, is the real analysis of the entry read as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {T : Type} [FloatOps T] [SoundFloatArithmetic T] [ExactLe T]
variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)] in
/-- One proposition analyzed on a float analyzer, read as reals, is the real analysis. -/
private theorem aux_analyzeKey_mapTime [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)]
    (obj : ReachSetAnalyzer T S n) (set : S n) (loc : ℕ) (lo hi : T)
    (p : String × AtomicProposition S n) : -- --- CONCL ---
    (obj.analyzeKey (𝕋 := 𝕋) set loc lo hi p).map (ReachSetAnalyzer.mapTime toReal) =
      (obj.mapTime toReal).analyzeKey (𝕋 := 𝕋) set loc (toReal lo) (toReal hi)
        p := by -- --- PROOF ---
  unfold ReachSetAnalyzer.analyzeKey
  rw [ReachSetAnalyzer.maskOk_mapTime]
  have hl : (obj.mapTime toReal).sigBuilder.lookup p.1 =
      (obj.sigBuilder.lookup p.1).map (FiniteKleeneSignalBuilder.mapTime toReal) :=
    lookup_map_snd _ _ _
  rw [hl]
  cases obj.sigBuilder.lookup p.1 with
  | none => rfl
  | some b =>
    simp only [Option.map_some, Option.bind_some]
    by_cases hm : obj.maskOk p.1 lo hi = true
    · rw [if_pos hm, if_pos hm]
      -- the marking as possibly true
      have ht : (if p.2.canBeTrue (𝕋 := 𝕋) set loc then
          (b.mapTime toReal).setPossiblyTrue? (toReal lo) (toReal hi)
          else some (b.mapTime toReal)) = (if p.2.canBeTrue (𝕋 := 𝕋) set loc then
          b.setPossiblyTrue? lo hi else some b).map (FiniteKleeneSignalBuilder.mapTime toReal) := by
        split_ifs
        · exact (FiniteKleeneSignalBuilder.setPossiblyTrue?_mapTime b lo hi).symm
        · rfl
      rw [ht]
      cases (if p.2.canBeTrue (𝕋 := 𝕋) set loc then b.setPossiblyTrue? lo hi else some b) with
      | none => rfl
      | some b1 =>
        simp only [Option.map_some, Option.bind_some]
        -- the marking as possibly false
        have hf : (if p.2.canBeFalse (𝕋 := 𝕋) set loc then
            (b1.mapTime toReal).setPossiblyFalse? (toReal lo) (toReal hi)
            else some (b1.mapTime toReal)) = (if p.2.canBeFalse (𝕋 := 𝕋) set loc then
            b1.setPossiblyFalse? lo hi else some b1).map
              (FiniteKleeneSignalBuilder.mapTime toReal) := by
          split_ifs
          · exact (FiniteKleeneSignalBuilder.setPossiblyFalse?_mapTime b1 lo hi).symm
          · rfl
        rw [hf]
        cases (if p.2.canBeFalse (𝕋 := 𝕋) set loc then b1.setPossiblyFalse? lo hi
          else some b1) with
        | none => rfl
        | some b2 =>
          simp only [Option.map_some]
          unfold ReachSetAnalyzer.mapTime
          simp only
          rw [replaceKey_map_snd]
    · rw [if_neg hm, if_neg hm]
      rfl

/-- One time interval analyzed on a float analyzer, read as reals, is the real analysis. -/
private theorem aux_analyzeTimeInterval_mapTime (obj : ReachSetAnalyzer T S n) (set : S n) (loc : ℕ)
    (lo hi : T) : -- --- CONCL ---
    (obj.analyzeTimeInterval (𝕋 := 𝕋) set loc lo hi).map (ReachSetAnalyzer.mapTime toReal) =
      (obj.mapTime toReal).analyzeTimeInterval (𝕋 := 𝕋) set loc (toReal lo)
        (toReal hi) := by -- --- PROOF ---
  unfold ReachSetAnalyzer.analyzeTimeInterval
  rw [foldlM_option_map _ (fun o p => o.analyzeKey (𝕋 := 𝕋) set loc (toReal lo) (toReal hi) p)
    (ReachSetAnalyzer.mapTime toReal) id
    (fun o p => aux_analyzeKey_mapTime o set loc lo hi p), List.map_id]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeSingle_mapTime (obj : ReachSetAnalyzer T S n)
    (R : ReachSetAnalyzer.Entry T S n) :
    (obj.analyzeSingle (𝕋 := 𝕋) R).map (ReachSetAnalyzer.mapTime toReal) =
      (obj.mapTime toReal).analyzeSingle (𝕋 := 𝕋) (R.mapTime toReal) := by
  -- the loop over the time intervals commutes with reading them as reals
  unfold ReachSetAnalyzer.analyzeSingle
  exact foldlM_option_map _ _ _ _ (fun o t => aux_analyzeTimeInterval_mapTime o
    t.set R.loc t.time.inf t.time.sup) _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
