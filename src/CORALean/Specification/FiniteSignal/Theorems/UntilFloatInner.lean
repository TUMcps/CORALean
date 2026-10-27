module

public import CORALean.Specification.FiniteSignal.Operations.Until
public import CORALean.Specification.FiniteSignal.Operations.UntilFloat
public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.CombineMapTime
public import CORALean.Specification.FiniteSignal.Theorems.CombineSpec
public import CORALean.Specification.FiniteSignal.Theorems.FindIntervalsMapTime
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorSpec
public import CORALean.Specification.FiniteSignal.Theorems.MkEqSomeIff
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime
public import CORALean.Specification.FiniteSignal.Theorems.PairsOfValid
public import CORALean.Specification.FiniteSignal.Theorems.TimeLeDuration
public import CORALean.Specification.FiniteSignal.Theorems.UntilSpec
public import CORALean.Specification.FiniteSignal.Theorems.ValueAtConsOfGe
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# A float until of finite signals is true only where the exact one is

If the left signal read as reals is valid and `eps ≥ 0`, then `untilFloat?` returns a signal only
where `until?` of the signals read as reals does, and the float one, read as reals, is true at a
time `t ∈ [0, dur]` only where the exact one is: each float piece of a pair of runs lies inside the
exact piece of the same runs read as reals, because its tolerance test passes only where the
exact one does and its bounds are rounded inward.

## Inputs
* `eps` – machine epsilon
* `lsig` – left signal
* `rsig` – right signal
* `p` – interval lower bound
* `q` – interval upper bound

## Hypotheses
* `heps` – the tolerance is nonnegative
* `hl` – the left signal read as reals is valid

## Conclusion
* a float `true` is an exact `true`
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A nonempty list of breakpoints holds a value everywhere. -/
private theorem aux_valueAt_isSome {T V : Type} [LinearOrder T] : ∀ (L : List (T × V)) (t : T),
    L ≠ [] → ∃ v, FiniteSignal.valueAt L t = some v
  | [], _, h => absurd rfl h
  | [p], t, _ => ⟨p.2, FiniteSignal.valueAt_singleton p t⟩
  | p :: x :: rest, t, _ => by
    by_cases ht : t < p.1
    · exact ⟨p.2, FiniteSignal.valueAt_cons_of_lt p _ t ht⟩
    · rw [FiniteSignal.valueAt_cons_of_ge p _ t ht (by simp)]
      exact aux_valueAt_isSome (x :: rest) t (by simp)


/-- A signal has a value in its range. -/
private theorem FiniteSignal.aux_at?_isSome {T V : Type} [LinearOrder T] [Zero T]
    (s : FiniteSignal T V) (hs : s.IsValid) (t : T) (h0 : 0 ≤ t) (h1 : t ≤ s.duration) :
    ∃ v, s.at? t = some v := by
  obtain ⟨b, v, rest, hq, -, -, -⟩ := FiniteSignal.pairs_of_valid s hs
  rw [FiniteSignal.at?_eq_valueAt s hs.2.1 t, if_pos ⟨h0, h1⟩, hq]
  exact aux_valueAt_isSome _ t (by simp)


/-- A float piece lies inside the exact piece of the same runs read as reals. -/
private theorem FiniteSignal.aux_untilPieceFloat_sub (eps p : 𝕋) (q : WithTop 𝕋)
    (L R : Real.Interval 𝕋) (heps : 0 ≤ toReal eps) (lo hi : 𝕋)
    (h : FiniteSignal.step_untilPieceFloat eps p q L R = some ⟨lo, hi⟩) : -- --- CONCL ---
    toReal lo < toReal hi ∧ ∃ lo' hi', FiniteSignal.untilPiece (toReal eps) (toReal p)
      (STLInterval.toEReal q) ⟨toReal L.inf, toReal L.sup⟩ ⟨toReal R.inf, toReal R.sup⟩ =
        some ⟨lo', hi'⟩ ∧ lo' ≤ toReal lo ∧ toReal hi ≤ hi' := by -- --- PROOF ---
  obtain ⟨Li, Ls⟩ := L
  obtain ⟨Ri, Rs⟩ := R
  simp only [FiniteSignal.step_untilPieceFloat] at h
  -- the meet of the runs is read exactly
  have hlb : toReal (if Li ≤ Ri then Ri else Li) = max (toReal Li) (toReal Ri) := by
    split_ifs with hh
    · exact (max_eq_right hh).symm
    · exact (max_eq_left (le_of_lt (not_le.1 hh))).symm
  have hub : toReal (if Ls ≤ Rs then Ls else Rs) = min (toReal Ls) (toReal Rs) := by
    split_ifs with hh
    · exact (min_eq_left hh).symm
    · exact (min_eq_right (le_of_lt (not_le.1 hh))).symm
  have hmax : ∀ a b : ℝ, ((max a b : ℝ) : EReal) = max (a : EReal) b :=
    fun a b => EReal.coe_strictMono.monotone.map_max
  have hmin : ∀ a b : ℝ, ((min a b : ℝ) : EReal) = min (a : EReal) b :=
    fun a b => EReal.coe_strictMono.monotone.map_min
  generalize (if Li ≤ Ri then Ri else Li) = lb at h hlb
  generalize (if Ls ≤ Rs then Ls else Rs) = ub at h hub
  -- the tolerance test passed, on a difference at least the exact one
  by_cases h1 : subUp lb ub ≤ eps
  swap
  · rw [if_pos h1] at h; exact absurd h (by simp)
  rw [if_neg (not_not.2 h1)] at h
  have h1' : toReal lb - toReal ub ≤ toReal eps := (sub_le_subUp lb ub).trans h1
  -- the ends of the meet, read exactly
  have hlo : toReal (if lb ≤ ub then lb else ub) = min (toReal lb) (toReal ub) := by
    split_ifs with hh
    · exact (min_eq_left hh).symm
    · exact (min_eq_right (le_of_lt (not_le.1 hh))).symm
  have hhi : toReal (if lb ≤ ub then ub else lb) = max (toReal lb) (toReal ub) := by
    split_ifs with hh
    · exact (max_eq_right hh).symm
    · exact (max_eq_left (le_of_lt (not_le.1 hh))).symm
  generalize (if lb ≤ ub then lb else ub) = m at h hlo
  generalize (if lb ≤ ub then ub else lb) = M at h hhi
  -- the float bounds of the piece and the exact ones they lie inside
  set ub'f : 𝕋 := if subDown M p ≤ Ls then subDown M p else Ls with hub'f
  have hY : toReal ub'f ≤ min (max (toReal lb) (toReal ub) - toReal p) (toReal Ls) := by
    rw [hub'f]
    have := subDown_le_sub M p
    split_ifs with hh
    · exact le_min (hhi ▸ this) hh
    · exact le_min (le_trans (le_of_lt (not_le.1 hh)) (hhi ▸ this)) le_rfl
  -- the exact lower bound of the piece, a real at most the float one
  obtain ⟨lb'f, X, h, hX, hXle⟩ : ∃ (lb'f : 𝕋) (X : ℝ),
      (if lb'f < ub'f then some (⟨lb'f, ub'f⟩ : Real.Interval 𝕋) else none) = some ⟨lo, hi⟩ ∧
      max (((min (toReal lb) (toReal ub) : ℝ) : EReal) - STLInterval.toEReal q)
        ((toReal Li : ℝ) : EReal) = (X : EReal) ∧ X ≤ toReal lb'f := by
    rcases q with _ | y
    · exact ⟨Li, toReal Li, h, by simp, le_rfl⟩
    · refine ⟨if subUp m y ≤ Li then Li else subUp m y,
        max (min (toReal lb) (toReal ub) - toReal y) (toReal Li), h, ?_, ?_⟩
      · rw [STLInterval.toEReal_some, ← EReal.coe_sub, ← hmax]
      · have := sub_le_subUp m y
        rw [hlo] at this
        split_ifs with hh
        · exact max_le (le_trans this hh) le_rfl
        · exact max_le this (le_of_lt (not_le.1 hh))
  -- the float piece is nonempty
  by_cases h2 : lb'f < ub'f
  swap
  · rw [if_neg h2] at h; exact absurd h (by simp)
  rw [if_pos h2, Option.some.injEq, Real.Interval.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h2' : toReal lb'f < toReal ub'f := h2
  refine ⟨h2', X, min (max (toReal lb) (toReal ub) - toReal p) (toReal Ls), ?_, hXle, hY⟩
  -- the exact piece: its tests pass, and its ends are in order
  have hXY : X < min (max (toReal lb) (toReal ub) - toReal p) (toReal Ls) :=
    lt_of_le_of_lt hXle (lt_of_lt_of_le h2' hY)
  unfold FiniteSignal.untilPiece
  dsimp only
  rw [← hlb, ← hub, if_neg (not_not.2 (by exact_mod_cast h1')), hX,
    show ((max (toReal lb) (toReal ub) : ℝ) : EReal) - ((toReal p : ℝ) : EReal) =
      ((max (toReal lb) (toReal ub) - toReal p : ℝ) : EReal) from (EReal.coe_sub _ _).symm,
    ← hmin, if_neg (not_not.2 (by rw [← EReal.coe_sub, EReal.coe_le_coe_iff]; linarith)), ← hmin,
    ← hmax, EReal.toReal_coe,
    EReal.toReal_coe, min_eq_left hXY.le, max_eq_right hXY.le]


omit [ExactLe 𝕋] in
/-- A valid signal has a value in its range, read as reals. -/
private theorem FiniteSignal.aux_mapTime_at?_isSome (s : FiniteSignal 𝕋 Bool)
    (hs : (s.mapTime toReal).IsValid) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ (s.mapTime toReal).duration) :
    ∃ v, (s.mapTime toReal).at? t = some v :=
  FiniteSignal.aux_at?_isSome _ hs t h0 h1


/-- The loop of `untilFloat?`, read as reals: every pair of runs adds the times of its piece. -/
private theorem aux_untilFloat_fold (eps p : 𝕋) (q : WithTop 𝕋) (dur : 𝕋) (h0 : 0 ≤ toReal dur) :
    ∀ (prs : List (Real.Interval 𝕋 × Real.Interval 𝕋)) (sig : FiniteSignal 𝕋 Bool),
      (sig.mapTime toReal).IsValid → (sig.mapTime toReal).duration = toReal dur →
      ∃ r, prs.foldlM (FiniteSignal.step_untilStepFloat eps p q dur) sig = some r ∧
        (r.mapTime toReal).IsValid ∧ (r.mapTime toReal).duration = toReal dur ∧
        ∀ t : ℝ, 0 ≤ t → t ≤ toReal dur → ∃ v, (r.mapTime toReal).at? t = some v ∧
          (v = true ↔ ((sig.mapTime toReal).at? t = some true ∨ ∃ LR ∈ prs, ∃ lo hi,
            FiniteSignal.step_untilPieceFloat eps p q LR.1 LR.2 = some ⟨lo, hi⟩ ∧
              toReal lo < toReal hi ∧ (0 < toReal hi ∧ toReal lo < toReal dur ∧ toReal lo ≤ t ∧
                (t < toReal hi ∨ toReal dur ≤ toReal hi))))
  | [], sig, hs, hd => by
    refine ⟨sig, rfl, hs, hd, fun t ht0 ht1 => ?_⟩
    obtain ⟨v, hv⟩ := FiniteSignal.aux_mapTime_at?_isSome sig hs t ht0 (hd ▸ ht1)
    exact ⟨v, hv, by simp [hv]⟩
  | LR :: rest, sig, hs, hd => by
    -- pairs of runs after `LR`, with the signal after it
    have hrest : ∀ sig' : FiniteSignal 𝕋 Bool, (sig'.mapTime toReal).IsValid →
        (sig'.mapTime toReal).duration = toReal dur →
        FiniteSignal.step_untilStepFloat eps p q dur sig LR = some sig' →
        ∃ r, (LR :: rest).foldlM (FiniteSignal.step_untilStepFloat eps p q dur) sig = some r ∧
          (r.mapTime toReal).IsValid ∧ (r.mapTime toReal).duration = toReal dur ∧
          ∀ t : ℝ, 0 ≤ t → t ≤ toReal dur → ∃ v, (r.mapTime toReal).at? t = some v ∧
            (v = true ↔ ((sig'.mapTime toReal).at? t = some true ∨ ∃ LR' ∈ rest, ∃ lo hi,
              FiniteSignal.step_untilPieceFloat eps p q LR'.1 LR'.2 = some ⟨lo, hi⟩ ∧
                toReal lo < toReal hi ∧ (0 < toReal hi ∧ toReal lo < toReal dur ∧
                  toReal lo ≤ t ∧ (t < toReal hi ∨ toReal dur ≤ toReal hi)))) :=
      fun sig' hv hdd hstep => by
        obtain ⟨r, hr1, hr2, hr3, hr4⟩ := aux_untilFloat_fold eps p q dur h0 rest sig' hv hdd
        refine ⟨r, ?_, hr2, hr3, hr4⟩
        rw [List.foldlM_cons, hstep]
        exact hr1
    -- the case of the piece of `LR`
    rcases hpc : FiniteSignal.step_untilPieceFloat eps p q LR.1 LR.2 with _ | ⟨lo, hi⟩
    · -- empty: the signal stays
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hrest sig hs hd
        (by simp [FiniteSignal.step_untilStepFloat, hpc])
      refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
      obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
      refine ⟨v, hv, hvi.trans ?_⟩
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hpc]
      simp
    · by_cases hlh : lo < hi
      · -- a piece of positive length: or-ed with its indicator
        have hlh' : toReal lo < toReal hi := hlh
        obtain ⟨ind', hind1, hind2, hind3, hind4⟩ :=
          FiniteSignal.indicator?_spec (toReal dur) (toReal lo) (toReal hi) true h0 hlh'
        rw [← FiniteSignal.indicator?_mapTime, Option.map_eq_some_iff] at hind1
        obtain ⟨ind, hind1, rfl⟩ := hind1
        obtain ⟨sig', hc1, hc2, hc3, hc4⟩ :=
          FiniteSignal.combine?_spec (fun x y => x || y) _ _ hs hind2
        rw [show [sig.mapTime toReal, ind.mapTime toReal] = [sig, ind].map
          (FiniteSignal.mapTime toReal) from rfl, ← FiniteSignal.combine?_mapTime,
          Option.map_eq_some_iff] at hc1
        obtain ⟨sig'', hc1, rfl⟩ := hc1
        -- the fact `hdd`
        have hdd : (sig''.mapTime toReal).duration = toReal dur := by
          rw [hc3, hd, hind3, min_self]
        obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hrest sig'' hc2 hdd (by
          simp [FiniteSignal.step_untilStepFloat, hpc, hlh, hind1, hc1])
        refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
        obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
        refine ⟨v, hv, ?_⟩
        -- the value of `sig''` at `t`
        obtain ⟨x, hx⟩ := FiniteSignal.aux_mapTime_at?_isSome sig hs t ht0 (hd ▸ ht1)
        have hy := hind4 t ht0 ht1
        have hok : t < (sig.mapTime toReal).duration ∧ t < (ind.mapTime toReal).duration ∨
            (sig.mapTime toReal).duration = (ind.mapTime toReal).duration ∧
              t = (sig.mapTime toReal).duration := by
          rcases ht1.lt_or_eq with h | h
          · exact Or.inl ⟨hd ▸ h, hind3 ▸ h⟩
          · exact Or.inr ⟨hd.trans hind3.symm, hd ▸ h⟩
        have hs' := hc4 t x _ hx hy hok
        rw [hs'] at hvi
        rw [hvi]
        simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hpc]
        simp only [Option.some.injEq, Bool.or_eq_true, hx, decide_eq_true_eq]
        simp [hlh', or_assoc]
      · -- a piece without length: the signal stays
        obtain ⟨r, hr1, hr2, hr3, hr4⟩ :=
          hrest sig hs hd (by simp [FiniteSignal.step_untilStepFloat, hpc, hlh])
        refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
        obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
        refine ⟨v, hv, hvi.trans ?_⟩
        simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hpc]
        have hlh' : ¬ toReal lo < toReal hi := hlh
        simp [hlh']


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.untilFloat?_inner (eps : 𝕋) (lsig rsig : FiniteSignal 𝕋 Bool) (p : 𝕋)
    (q : WithTop 𝕋) (heps : 0 ≤ toReal eps)
    (hl : (lsig.mapTime toReal).IsValid) : -- --- CONCL ---
    ∀ r ∈ FiniteSignal.untilFloat? eps lsig p q rsig,
      ∃ e, FiniteSignal.until? (toReal eps) (lsig.mapTime toReal) (toReal p)
        (STLInterval.toEReal q) (rsig.mapTime toReal) = some e ∧
        ∀ t : ℝ, 0 ≤ t → t ≤ toReal lsig.duration →
          (r.mapTime toReal).at? t = some true → e.at? t = some true := by -- --- PROOF ---
  intro r hr
  have hdl := FiniteSignal.duration_mapTime toReal toReal_zero_eq lsig
  have hdr := FiniteSignal.duration_mapTime toReal toReal_zero_eq rsig
  -- the durations agree, so the exact until returns a signal
  unfold FiniteSignal.untilFloat? at hr
  by_cases hd : TimeOrder.Eqv lsig.duration rsig.duration
  swap
  · rw [if_pos hd] at hr; exact absurd hr (by simp)
  rw [if_neg (not_not.2 hd)] at hr
  have hd' : (lsig.mapTime toReal).duration = (rsig.mapTime toReal).duration := by
    rw [hdl, hdr]; exact hd
  obtain ⟨e, he, -, -, hE⟩ := FiniteSignal.until?_spec (toReal eps) _ _ (toReal p)
    (STLInterval.toEReal q) hl hd'
  refine ⟨e, he, fun t ht0 ht1 htrue => ?_⟩
  -- the duration is nonnegative
  obtain ⟨hmem, -⟩ := FiniteSignal.time_le_duration _ hl
  have h0 : 0 ≤ toReal lsig.duration := hdl ▸ hl.2.2.2.2 _ hmem
  -- the float signal starts as the constant false signal
  have hv0 : (⟨[toReal lsig.duration], [false]⟩ : FiniteSignal ℝ Bool).IsValid :=
    ⟨by simp, by simp, by simp, by simp, fun t ht => by simp at ht; rw [ht]; exact h0⟩
  obtain ⟨s0, hs0, hs0'⟩ : ∃ s0, FiniteSignal.mk? [lsig.duration] [false] = some s0 ∧
      s0.mapTime toReal = ⟨[toReal lsig.duration], [false]⟩ := by
    have h := (FiniteSignal.mk?_eq_some_iff [toReal lsig.duration] [false]
      ⟨[toReal lsig.duration], [false]⟩).mpr ⟨rfl, rfl, hv0⟩
    rw [← List.map_singleton (f := toReal), ← FiniteSignal.mk?_mapTime,
      Option.map_eq_some_iff] at h
    exact h
  rw [hs0, Option.bind_some] at hr
  obtain ⟨r', hr1, -, -, hr4⟩ := aux_untilFloat_fold eps p q lsig.duration h0 _ s0
    (hs0' ▸ hv0) (by rw [hs0']; simp [FiniteSignal.duration])
  obtain rfl : r' = r := Option.some.inj (hr1.symm.trans hr)
  obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
  obtain rfl : v = true := Option.some.inj (hv.symm.trans htrue)
  rcases hvi.1 rfl with hf | ⟨LR, hLR, lo, hi, hpc, -, hpos, hlo, hlt, hhi⟩
  · -- the constant false signal is false at `t`
    rw [hs0', FiniteSignal.at?_eq_valueAt _ hv0.2.1 t, if_pos ⟨ht0, by
      simpa [FiniteSignal.duration] using ht1⟩] at hf
    simp [FiniteSignal.pairs, FiniteSignal.valueAt] at hf
  · -- a pair of runs whose float piece holds `t`: its exact piece holds it too
    simp only [List.mem_flatMap, List.mem_map] at hLR
    obtain ⟨L, hL, R, hR, rfl⟩ := hLR
    obtain ⟨hlh, lo', hi', hpiece, hlo', hhi'⟩ :=
      FiniteSignal.aux_untilPieceFloat_sub eps p q L R heps lo hi hpc
    rw [hdl] at hE
    refine (hE t ht0 ht1).2 ⟨_, ?_, _, ?_, lo', hi', hpiece, by linarith,
      by linarith, by linarith, by linarith, ?_⟩
    · rw [FiniteSignal.findIntervals_mapTime toReal toReal_zero_eq]
      exact List.mem_map_of_mem hL
    · rw [FiniteSignal.findIntervals_mapTime toReal toReal_zero_eq]
      exact List.mem_map_of_mem hR
    · rcases hhi with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
