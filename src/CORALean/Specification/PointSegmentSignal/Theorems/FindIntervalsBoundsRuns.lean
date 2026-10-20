module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervalsBounds
public import CORALean.Specification.PointSegmentSignal.Theorems.ListRunsOfMatlabDiff
public import Mathlib.Order.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# `findIntervals` returns the maximal runs of values

The bounds `findIntervals` builds are those of pairs `(r, f)` of one-based value indices: each run
`r, ..., f` satisfies `cond` throughout, is preceded and followed by a value that does not, and
every value that satisfies `cond` lies in a run. The bounds are `precTimeAtValIdx r`,
`succTimeAtValIdx f`.

## Inputs
* `T` – time type
* `s` – signal
* `cond` – condition on values

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the intervals are those of the maximal runs of satisfying values
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Inside the array the entry of a mapped array is the map of the entry. -/
theorem aux_map_getD {T : Type} (s : PointSegmentSignal T) (cond : Bool → Bool) (i : ℕ)
    (hi : i < s.values.length) :
    (s.values.map cond).getD i false = cond (s.values.getD i false) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- Inside the array the default of `getD` does not matter. -/
theorem aux_getD_default (tk : List Bool) (i : ℕ) (hi : i < tk.length) (d d' : Bool) :
    tk.getD i d = tk.getD i d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- Pairing the rising edges with the falling edges, then the last rising edge with the end. -/
theorem aux_zip_trail {α : Type} (g : ℕ → ℕ → α) (trail : ℕ → α) (N : ℕ)
    (htrail : ∀ r, g r N = trail r) : -- --- CONCL ---
    ∀ (F R : List ℕ), R.length ≤ F.length + 1 →
    (R.zip F).map (fun x => g x.1 x.2) ++
      (if F.length < R.length then (R.getLast?.map trail).toList else []) =
      (R.zip (F ++ [N])).map (fun x => g x.1 x.2) := by -- --- PROOF ---
  intro F
  induction F with
  | nil =>
    intro R hR
    match R, hR with
    | [], _ => simp
    | [r], _ => simp [htrail]
  -- the first pair, then the rest
  | cons f F ih =>
    intro R hR
    match R with
    | [] => simp
    | r :: R' =>
      have := ih R' (by simp at hR; omega)
      simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.length_cons]
      by_cases h : F.length < R'.length
      · have hne : R' ≠ [] := by rintro rfl; simp at h
        obtain ⟨b, R'', rfl⟩ := List.exists_cons_of_ne_nil hne
        rw [if_pos h] at this
        rw [if_pos (by simp at h ⊢; omega), List.getLast?_cons_cons]
        rw [← this]
      · rw [if_neg h] at this
        rw [if_neg (by simp; omega)]
        simpa using this

/-- The first point of a valid signal is `0`. -/
theorem aux_prec_one {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) : -- --- CONCL ---
    s.precTimeAtValIdx 1 = (0, true) := by -- --- PROOF ---
  have h := hs.2.2.1
  have : s.timePoints.getD 0 0 = 0 := by
    cases hp : s.timePoints with
    | nil => simp [hp] at h
    | cons a l => simp [hp] at h; simp [h]
  simpa [PointSegmentSignal.precTimeAtValIdx] using this

/-- Past the last value the time is `inf`, which is open. -/
theorem aux_succ_len {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) : -- --- CONCL ---
    s.succTimeAtValIdx s.values.length = (⊤, false) := by -- --- PROOF ---
  have h := hs.2.1
  simp only [PointSegmentSignal.succTimeAtValIdx, PointSegmentSignal.length]
  rw [if_pos (by omega)]
  simp only [Prod.mk.injEq, true_and, decide_eq_false_iff_not]
  omega

/-- `findIntervals` is the runs paired off, as bounds. -/
theorem aux_findIntervalsBounds_eq {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (cond : Bool → Bool) (F R R' : List ℕ)
    (hF : F = List.matlabFind (· == (-1 : ℤ)) (List.matlabDiff (s.values.map cond)))
    (hR : R = (List.matlabFind (· == (1 : ℤ)) (List.matlabDiff (s.values.map cond))).map (· + 1))
    (hR' : R' = if (s.values.map cond).head? = some true then 1 :: R else R)
    (hlen : R'.length ≤ F.length + 1) : -- --- CONCL ---
    s.findIntervalsBounds cond = (R'.zip (F ++ [s.values.length])).map (fun x =>
      ((s.precTimeAtValIdx x.1).1, (s.succTimeAtValIdx x.2).1, (s.precTimeAtValIdx x.1).2,
        (s.succTimeAtValIdx x.2).2)) := by -- --- PROOF ---
  unfold PointSegmentSignal.findIntervalsBounds
  simp only [← hF, ← hR]
  -- the pairing lemma, for the bounds of an interval and the open last one
  have hZ := fun F' R'' (h : R''.length ≤ F'.length + 1) => aux_zip_trail
    (fun r f => ((s.precTimeAtValIdx r).1, (s.succTimeAtValIdx f).1, (s.precTimeAtValIdx r).2,
      (s.succTimeAtValIdx f).2))
    (fun r => ((s.precTimeAtValIdx r).1, (⊤ : WithTop T), (s.precTimeAtValIdx r).2, false))
    s.values.length (fun r => by simp [aux_succ_len s hs]) F' R'' h
  subst hR'
  by_cases hh : (s.values.map cond).head? = some true
  · rw [if_pos hh] at hlen ⊢
    rw [if_pos hh]
    cases F with
    | nil =>
      have hR0 : R = [] := by simpa using hlen
      subst hR0
      simp [aux_prec_one s hs, aux_succ_len s hs]
    | cons f₁ F' =>
      have h2 := hZ F' R (by simp at hlen; omega)
      simp only [List.zip_cons_cons, List.cons_append, List.map_cons, aux_prec_one s hs]
      rw [h2]
  · rw [if_neg hh] at hlen ⊢
    rw [if_neg hh, hZ F R (by omega)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intervals of `findIntervals` are the maximal runs of values satisfying `cond`. -/
theorem PointSegmentSignal.findIntervalsBounds_runs {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (cond : Bool → Bool) : -- --- CONCL ---
    ∃ runs : List (ℕ × ℕ),
      s.findIntervalsBounds cond = runs.map (fun x =>
        ((s.precTimeAtValIdx x.1).1, (s.succTimeAtValIdx x.2).1, (s.precTimeAtValIdx x.1).2,
          (s.succTimeAtValIdx x.2).2)) ∧
      (∀ p ∈ runs, 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ s.values.length ∧
        (∀ m, p.1 ≤ m → m ≤ p.2 → cond (s.values.getD (m - 1) false) = true) ∧
        (2 ≤ p.1 → cond (s.values.getD (p.1 - 2) false) = false) ∧
        (p.2 < s.values.length → cond (s.values.getD p.2 false) = false)) ∧
      (∀ m, 1 ≤ m → m ≤ s.values.length → cond (s.values.getD (m - 1) false) = true →
        ∃ p ∈ runs, p.1 ≤ m ∧ m ≤ p.2) := by -- --- PROOF ---
  obtain ⟨tk, htk⟩ : ∃ tk, tk = s.values.map cond := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = List.matlabFind (· == (-1 : ℤ)) (List.matlabDiff tk) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (List.matlabFind (· == (1 : ℤ)) (List.matlabDiff tk)).map (· + 1) :=
    ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R', R' = if tk.head? = some true then 1 :: R else R := ⟨_, rfl⟩
  -- the array `take` is not empty, and has the length of `values`
  have hNpos : 1 ≤ s.values.length := by
    have := List.length_pos_iff.2 hs.1; have := hs.2.1; omega
  have htkN : tk.length = s.values.length := by rw [htk]; simp
  have hne : tk ≠ [] := by intro h; rw [h] at htkN; simp at htkN; omega
  -- the runs of `true` of the array `take`
  obtain ⟨hl2, hT1, hT2⟩ := List.runs_of_matlabDiff tk hne F R R' hF hR hR'
  refine ⟨R'.zip (F ++ [s.values.length]), ?_, ?_, ?_⟩
  · exact aux_findIntervalsBounds_eq s hs cond F R R' (by rw [hF, htk]) (by rw [hR, htk])
      (by rw [hR', htk]) hl2
  · rw [← htkN]
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hT1 p hp
    refine ⟨h1, h2, h3, fun m hm1 hm2 => ?_, fun h => ?_, fun h => ?_⟩
    · have := h4 m hm1 hm2
      rwa [htk, aux_map_getD s cond _ (by omega)] at this
    · have := h5 h
      rwa [aux_getD_default tk _ (by omega) true false, htk,
        aux_map_getD s cond _ (by omega)] at this
    · have := h6 h
      rwa [aux_getD_default tk _ (by omega) true false, htk,
        aux_map_getD s cond _ (by omega)] at this
  -- every value that satisfies `cond` lies in a run
  · rw [← htkN]
    intro m hm1 hm2 hm
    refine hT2 m hm1 hm2 ?_
    rwa [htk, aux_map_getD s cond _ (by omega)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
