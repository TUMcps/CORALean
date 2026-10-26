module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Global.FoldlMOptionMap
public import CORALean.Global.LookupMapSnd
public import CORALean.Global.MapMOptionMap
public import CORALean.Global.ReplaceKeyMapSnd
public import CORALean.Specification.FiniteSignal.Theorems.CombineMapTime
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime
public import CORALean.Specification.TrajectoryAnalyzer.Operations.Basic
public import CORALean.Specification.TrajectoryAnalyzer.Theorems.AnalyzeSpec

@[expose] public section

/-!
# What `analyze` computes over float time points

A trajectory over a float scalar `T` compares its time points exactly (`TimeOrder`), so `analyze`
read through `toReal` is `analyze` of the trajectory read as reals, and what `analyze_spec` says of
that one holds of the float result: the signal of each proposition is true at a time exactly when
the proposition holds at a point of the simulation whose interval covers the time.

## Inputs
* `obj` – trajectory analyzer
* `s` – realization

## Hypotheses
* `hnd` – the proposition keys are distinct
* `ht` – the trajectory has time points
* `hsorted` – the time points, read as reals, strictly increase
* `hnn` – the time points are nonnegative

## Conclusion
* `analyze` returns signals that, read as reals, are true exactly at the covered times
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {T : Type} [FloatOps T] [SoundFloatArithmetic T] [ExactLe T]
variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]
  [OfScalarPoint 𝕋 S] [∀ k, Contains (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ k, ContSet (S k) (Vec ℝ k)] [OfScalarPoint 𝕋 S] [∀ k, Contains (S k) (S k)] in
/-- Marking a float signal true on an interval, read as reals, is the real marking. -/
private theorem aux_markKey_mapTime (dur lo hi : T) (sigs : List (String × FiniteSignal T Bool))
    (k : String) : -- --- CONCL ---
    (TrajectoryAnalyzer.markKey dur lo hi sigs k).map
        (List.map fun p => (p.1, p.2.mapTime toReal)) =
      TrajectoryAnalyzer.markKey (toReal dur) (toReal lo) (toReal hi)
        (sigs.map fun p => (p.1, p.2.mapTime toReal)) k := by -- --- PROOF ---
  unfold TrajectoryAnalyzer.markKey
  rw [lookup_map_snd, ← FiniteSignal.indicator?_mapTime]
  cases sigs.lookup k with
  | none => rfl
  | some sig =>
    cases hind : FiniteSignal.indicator? dur lo hi true with
    | none => rfl
    | some ind =>
      simp only [Option.map_some, Option.bind_some]
      have hc := FiniteSignal.combine?_mapTime (· || ·) [sig, ind]
      simp only [List.map_cons, List.map_nil] at hc
      rw [← hc]
      cases FiniteSignal.combine? (· || ·) [sig, ind] with
      | none => rfl
      | some sig' => simp only [Option.map_some, replaceKey_map_snd]

/-- One interval of a float trajectory analyzed, read as reals, is the real analysis. -/
private theorem aux_analyzeInterval_mapTime (obj : TrajectoryAnalyzer T 𝕋 S n) (s : ℕ) (dur : T)
    (sigs : List (String × FiniteSignal T Bool)) (l : ℕ) : -- --- CONCL ---
    (obj.analyzeInterval s dur sigs l).map (List.map fun p => (p.1, p.2.mapTime toReal)) =
      (obj.mapTime toReal).analyzeInterval s (toReal dur)
        (sigs.map fun p => (p.1, p.2.mapTime toReal)) l := by -- --- PROOF ---
  unfold TrajectoryAnalyzer.analyzeInterval
  -- the bounds of the interval are the float ones read as reals
  have hg : ∀ j, (obj.traj.t.map toReal).getD j 0 = toReal (obj.traj.t.getD j 0) := fun j => by
    rw [← toReal_zero_eq (𝕋 := T), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases obj.traj.t[j]? <;> rfl
  simp only [TrajectoryAnalyzer.mapTime, hg]
  -- every proposition marks the same interval
  have key := foldlM_option_map (fun sigs (p : String × AtomicProposition S n) =>
    if p.2.evaluatePoint (obj.traj.x l s)
      (if obj.traj.loc ≠ [] then obj.traj.loc.getD (l - 1) 0 else 1) = true then
      TrajectoryAnalyzer.markKey dur (obj.traj.t.getD (l - 1) 0) (obj.traj.t.getD l 0) sigs p.1
    else some sigs) (fun sigs (p : String × AtomicProposition S n) =>
    if p.2.evaluatePoint (obj.traj.x l s)
      (if obj.traj.loc ≠ [] then obj.traj.loc.getD (l - 1) 0 else 1) = true then
      TrajectoryAnalyzer.markKey (toReal dur) (toReal (obj.traj.t.getD (l - 1) 0))
        (toReal (obj.traj.t.getD l 0)) sigs p.1
    else some sigs) (List.map fun p => (p.1, p.2.mapTime toReal)) id (fun sigs p => by
      simp only [id]
      by_cases hev : p.2.evaluatePoint (obj.traj.x l s)
          (if obj.traj.loc ≠ [] then obj.traj.loc.getD (l - 1) 0 else 1) = true
      · rw [if_pos hev, if_pos hev]; exact aux_markKey_mapTime _ _ _ _ _
      · rw [if_neg hev, if_neg hev]; rfl) obj.aps sigs
  rwa [List.map_id] at key

/-- A float trajectory analyzed, read as reals, is the real analysis of the trajectory read as
reals. -/
private theorem aux_analyze_mapTime (obj : TrajectoryAnalyzer T 𝕋 S n) (s : ℕ) : -- --- CONCL ---
    (obj.analyze s).map (List.map fun p => (p.1, p.2.mapTime toReal)) =
      (obj.mapTime toReal).analyze s := by -- --- PROOF ---
  unfold TrajectoryAnalyzer.analyze
  simp only [TrajectoryAnalyzer.mapTime, List.getLast?_map, List.length_map]
  cases obj.traj.t.getLast? with
  | none => rfl
  | some dur =>
    simp only [Option.map_some, Option.bind_some]
    -- the initial signals are the float ones read as reals
    have hmk : ∀ a : String × AtomicProposition S n, ((FiniteSignal.mk? [dur] [false]).map
        fun sig => (a.1, sig)).map (fun p => (p.1, p.2.mapTime toReal)) =
        (FiniteSignal.mk? [toReal dur] [false]).map fun sig => (a.1, sig) := by
      intro a
      rw [Option.map_map, show [toReal dur] = [dur].map toReal from rfl,
        ← FiniteSignal.mk?_mapTime, Option.map_map]
      rfl
    have hm := mapM_option_map (fun p : String × AtomicProposition S n =>
      (FiniteSignal.mk? [dur] [false]).map fun sig => (p.1, sig))
      (fun p => (p.1, p.2.mapTime toReal)) obj.aps
    simp only [hmk] at hm
    rw [← hm]
    cases obj.aps.mapM (fun p => (FiniteSignal.mk? [dur] [false]).map fun sig => (p.1, sig)) with
    | none => rfl
    | some sigs =>
      simp only [Option.map_some, Option.bind_some]
      -- and so is every interval of the loop
      have key := foldlM_option_map (fun sigs l => obj.analyzeInterval s dur sigs l)
        (fun sigs l => (obj.mapTime toReal).analyzeInterval s (toReal dur) sigs l)
        (List.map fun p => (p.1, p.2.mapTime toReal)) id
        (fun sigs l => aux_analyzeInterval_mapTime obj s dur sigs l)
        (List.range' 1 (obj.traj.t.length - 1)) sigs
      rw [List.map_id] at key
      exact key


-- =======================================  MAIN THEOREM  ======================================= --

theorem TrajectoryAnalyzer.analyze_spec_mapTime (obj : TrajectoryAnalyzer T 𝕋 S n) (s : ℕ)
    (hnd : (obj.aps.map Prod.fst).Nodup) (ht : obj.traj.t ≠ [])
    (hsorted : (obj.traj.t.map toReal).Pairwise (· < ·))
    (hnn : ∀ x ∈ obj.traj.t, 0 ≤ toReal x) : -- --- CONCL ---
    ∃ dur sigs, obj.traj.t.getLast? = some dur ∧ obj.analyze s = some sigs ∧
      TrajectoryAnalyzer.SignalsRepresent obj.aps (toReal dur)
        (sigs.map fun p => (p.1, p.2.mapTime toReal)) (fun k τ =>
          ∃ l ∈ List.range' 1 (obj.traj.t.length - 1),
            (obj.mapTime toReal).IsTrueAt s (toReal dur) k l τ) := by -- --- PROOF ---
  -- what `analyze_spec` says of the trajectory read as reals
  obtain ⟨dur', sigs', hl, ha, hr⟩ := TrajectoryAnalyzer.analyze_spec (obj.mapTime toReal) s hnd
    (by simpa [TrajectoryAnalyzer.mapTime] using ht) hsorted
    (by simpa [TrajectoryAnalyzer.mapTime] using hnn)
  -- the duration and the signals are the float ones read as reals
  have hl' : (obj.traj.t.getLast?).map toReal = some dur' := by
    rw [← List.getLast?_map]; exact hl
  obtain ⟨dur, hdur, rfl⟩ := Option.map_eq_some_iff.mp hl'
  have ha' := aux_analyze_mapTime obj s
  rw [ha] at ha'
  obtain ⟨sigs, hsigs, rfl⟩ := Option.map_eq_some_iff.mp ha'
  refine ⟨dur, sigs, hdur, hsigs, ?_⟩
  simpa [TrajectoryAnalyzer.mapTime] using hr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
