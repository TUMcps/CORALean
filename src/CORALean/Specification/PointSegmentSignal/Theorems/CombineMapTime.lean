module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Combine

@[expose] public section

/-!
# Point-wise combination at a float time type, read as reals

Over a float scalar `𝕋` `combine` finds the smallest unconsumed time and the inputs at it by
exact comparisons (`TimeOrder`), so the float result read through `toReal` is the combination of the
inputs read as reals.

## Inputs
* `κ` – index type of the outputs
* `op` – pointwise operator on Boolean values
* `sig` – input signals
* `i` – output index

## Hypotheses
* none

## Conclusion
* combining commutes with reading the time points as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {ι : Type} [FinEnum ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [FinEnum ι] in
/-- The smallest of a list of times read as reals is the smallest float one read as a real. -/
private theorem PointSegmentSignal.aux_foldMin_mapTime (f : ι → WithTop 𝕋)
    (l : List ι) : -- --- CONCL ---
    l.foldr (fun k m => if (f k).map toReal ≤ m then (f k).map toReal else m) ⊤ =
      (l.foldr (fun k m => if f k ≤ m then f k else m) ⊤).map toReal := by -- --- PROOF ---
  -- one comparison at a time, each of the reals the times denote
  have hle : ∀ a b : WithTop 𝕋, a.map toReal ≤ b.map toReal ↔ a ≤ b := fun a b => by
    cases a <;> cases b
    · exact iff_of_true le_top le_top
    · exact iff_of_false (WithTop.not_top_le_coe _) (WithTop.not_top_le_coe _)
    · exact iff_of_true le_top le_top
    · show ((toReal _ : ℝ) : WithTop ℝ) ≤ ((toReal _ : ℝ) : WithTop ℝ) ↔ _
      rw [WithTop.coe_le_coe, WithTop.coe_le_coe]; exact Iff.rfl
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    by_cases h : f k ≤ l.foldr (fun k m => if f k ≤ m then f k else m) ⊤
    · rw [if_pos ((hle _ _).mpr h), if_pos h]
    · rw [if_neg (mt (hle _ _).mp h), if_neg h]

/-- One pass after another, the loop on the signals read as reals is the float loop read as
reals. -/
private theorem PointSegmentSignal.aux_combineLoop_mapTime (op : (ι → Bool) → Bool)
    (sig : ι → PointSegmentSignal 𝕋) (fuel : ℕ) : -- --- CONCL ---
    ∀ (inIdx : ι → ℕ) (tp : List 𝕋) (val : List Bool),
      PointSegmentSignal.combineLoop op (fun k => (sig k).mapTime toReal) fuel inIdx
          (tp.map toReal) val =
        ((PointSegmentSignal.combineLoop op sig fuel inIdx tp val).1.map toReal,
          (PointSegmentSignal.combineLoop op sig fuel inIdx tp val).2) := by -- --- PROOF ---
  -- the lengths, the times and the values read off the inputs are the float ones
  have hl : ∀ k, ((sig k).mapTime toReal).length = (sig k).length := fun k => by
    simp [PointSegmentSignal.length, PointSegmentSignal.mapTime]
  have ht : ∀ k i, ((sig k).mapTime toReal).timeOrInf i = ((sig k).timeOrInf i).map toReal :=
    fun k i => by
      unfold PointSegmentSignal.timeOrInf
      rw [hl]
      split_ifs
      · rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        simp only [PointSegmentSignal.mapTime, List.getElem?_map]
        cases (sig k).timePoints[i - 1]? <;> rfl
      · rfl
  have he : ∀ a b : WithTop 𝕋, TimeOrder.IsEqvTop (a.map toReal) (b.map toReal) ↔
      TimeOrder.IsEqvTop a b := fun a b => by
    cases a <;> cases b <;> exact Iff.rfl
  have hd : ∀ m : WithTop 𝕋, (m.map toReal).untopD 0 = toReal (m.untopD 0) := fun m => by
    cases m <;> simp [toReal_zero_eq]
  -- one pass at a time
  induction fuel with
  | zero => intro inIdx tp val; rfl
  | succ fuel ih =>
    intro inIdx tp val
    rw [PointSegmentSignal.combineLoop, PointSegmentSignal.combineLoop]
    simp only [hl]
    by_cases hc : ∃ k, inIdx k ≤ (sig k).length
    · rw [if_pos hc, if_pos hc]
      -- the times, the smallest one and the values at it are the float ones
      have hp : ∀ k i, ((sig k).mapTime toReal).pointValue i = (sig k).pointValue i :=
        fun _ _ => rfl
      have hq : ∀ k i, ((sig k).mapTime toReal).precIntervalValue i =
          (sig k).precIntervalValue i := fun _ _ => rfl
      have hs : ∀ k i, ((sig k).mapTime toReal).succIntervalValue i =
          (sig k).succIntervalValue i := fun _ _ => rfl
      simp only [ht, PointSegmentSignal.aux_foldMin_mapTime, he, hp, hq, hs, ne_eq,
        List.map_eq_nil_iff]
      rw [apply_ite (fun r : List 𝕋 × List Bool => (r.1.map toReal, r.2))]
      -- the same case on both sides
      split_ifs with hk
      · exact ih _ _ _
      · rw [hd, ← List.map_singleton, ← List.map_append]; exact ih _ _ _
    · rw [if_neg hc, if_neg hc]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.combine_mapTime {κ : Type} (op : (ι → Bool) → κ → Bool)
    (sig : ι → PointSegmentSignal 𝕋) (i : κ) : -- --- CONCL ---
    (PointSegmentSignal.combine op sig i).mapTime toReal =
      PointSegmentSignal.combine op (fun k => (sig k).mapTime toReal) i := by -- --- PROOF ---
  -- the loop from no output, the fuel being the same
  have hl : ∀ k, ((sig k).mapTime toReal).length = (sig k).length := fun k => by
    simp [PointSegmentSignal.length, PointSegmentSignal.mapTime]
  unfold PointSegmentSignal.combine
  simp only [hl]
  rw [show ([] : List ℝ) = ([] : List 𝕋).map toReal from rfl,
    PointSegmentSignal.aux_combineLoop_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
