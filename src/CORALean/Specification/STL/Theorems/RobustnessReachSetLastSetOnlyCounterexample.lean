module

public import CORALean.Specification.STL.Operations.RobustnessReachSetGloballyCora
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# CORA's `stl/robustness` on a reach set is positive for a violated `G_[0,3/2] x > 0`

`robustness(globally(x(1) > 0, interval(0,1.5)), R)` with `R` the reach set of `ẋ = 2` from
`[-1, -1/2]` on the non-uniform steps `0, 1, 2, 4`: time-point sets `[-1,-1/2]`, `[1,3/2]`,
`[3,7/2]`, `[7,15/2]` and time-interval sets `[-1,3/2]`, `[1,7/2]`, `[3,15/2]`, each the exact
set of the flow (built directly; CORA's adaptive `reach` gives non-uniform steps, as does any
`R` with several branches, which takes the same branch, l. 287). `min(dt) = 1`, so `t =
linspace(0,1.5,2)` is a single window `[0,1.5]`; `aux_findReachSets` returns the time points `0`,
`1` and the time intervals `[0,1]`, `[1,2]`, and the loop of l. 292-297 keeps the last one's
robustness, the distance `1 + eps` of `[1,7/2]` from `x ≤ -eps`, where the minimum over the four
is `-1 + eps`. CORA returns `1 + eps > 0`, satisfied ("val > 0 if satisfied"), while the run
`x(s) = -1 + 2s` from `x(0) = -1` lies in the set of `[0,1]` and violates `x > 0` at `s = 0`.
The time test `meets` is any one true on meeting intervals and false on intervals `1/2` apart
(CORA's tolerance is `1e-8`); the set tests are true on meeting sets, the exact one false on sets
`1/2` apart; `ε` is any shift in `[0, 1/2)`, CORA's `eps` among them. Real arithmetic; every
comparison holds by a margin of at least `1/2`. Not run in MATLAB.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.robustnessReachSetGloballyCora_lastSetOnly_counterexample
    (meets : Real.Interval ℝ → Real.Interval ℝ → Bool)
    (hmeets : ∀ a b : Real.Interval ℝ, a.inf ≤ b.sup → b.inf ≤ a.sup → meets a b = true)
    (hsep : ∀ a b : Real.Interval ℝ, a.sup + 1 / 2 ≤ b.inf ∨ b.sup + 1 / 2 ≤ a.inf →
        meets a b = false)
    (isectApprox isectExact : Real.Interval ℝ → ℝ → Bool)
    (happrox : ∀ S b, S.inf ≤ b → isectApprox S b = true)
    (hexact : ∀ S b, S.inf ≤ b → isectExact S b = true)
    (hexact' : ∀ S b, b + 1 / 2 ≤ S.inf → isectExact S b = false)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    let tp : List ℝ := [0, 1, 2, 4]                                     -- R.timePoint.time
    let Xp : List (Real.Interval ℝ) := [⟨-1, -1 / 2⟩, ⟨1, 3 / 2⟩, ⟨3, 7 / 2⟩, ⟨7, 15 / 2⟩]
    let ti : List (Real.Interval ℝ) := [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 4⟩]  -- R.timeInterval.time
    let Xi : List (Real.Interval ℝ) := [⟨-1, 3 / 2⟩, ⟨1, 7 / 2⟩, ⟨3, 15 / 2⟩]
    -- a run of `ẋ = 2` from the initial set stays in the set of `[0,1]` and violates `x > 0`
    (∃ x : ℝ → ℝ, -1 ≤ x 0 ∧ x 0 ≤ -1 / 2 ∧ (∀ s, HasDerivAt x 2 s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, -1 ≤ x s ∧ x s ≤ 3 / 2) ∧ ¬ 0 < x 0) ∧
    -- CORA's robustness is `1 + eps`, positive: satisfied
    STL.robustnessReachSetGloballyCora meets isectApprox isectExact ε tp Xp ti Xi (3 / 2) =
      some (1 + ε) ∧ 0 < 1 + ε := by -- --- PROOF ---
  intro tp Xp ti Xi
  refine ⟨⟨fun s => -1 + 2 * s, by norm_num, by norm_num, fun s => ?_, fun s hs => ?_,
    by norm_num⟩, ?_, by linarith⟩
  · have h := ((hasDerivAt_id s).const_mul (2 : ℝ)).const_add (-1 : ℝ)
    rw [mul_one] at h
    exact h
  · obtain ⟨h0, h1⟩ := hs; constructor <;> linarith
  -- the window is `[0, 3/2]`: time points `0, 1` and time intervals `[0,1]`, `[1,2]` meet it
  have hN : ⌈(3 / 2 : ℝ)⌉₊ = 2 := by rw [Nat.ceil_eq_iff] <;> norm_num
  have m1 : meets ⟨0, 0⟩ ⟨0, 3 / 2⟩ = true := hmeets _ _ (by norm_num) (by norm_num)
  have m2 : meets ⟨1, 1⟩ ⟨0, 3 / 2⟩ = true := hmeets _ _ (by norm_num) (by norm_num)
  have m3 : meets ⟨2, 2⟩ ⟨0, 3 / 2⟩ = false := hsep _ _ (Or.inr (by norm_num))
  have m4 : meets ⟨4, 4⟩ ⟨0, 3 / 2⟩ = false := hsep _ _ (Or.inr (by norm_num))
  have m5 : meets ⟨0, 1⟩ ⟨0, 3 / 2⟩ = true := hmeets _ _ (by norm_num) (by norm_num)
  have m6 : meets ⟨1, 2⟩ ⟨0, 3 / 2⟩ = true := hmeets _ _ (by norm_num) (by norm_num)
  have m7 : meets ⟨2, 4⟩ ⟨0, 3 / 2⟩ = false := hsep _ _ (Or.inr (by norm_num))
  have a1 : isectApprox ⟨-1, -2⁻¹⟩ (-ε) = true := happrox _ _ (by simp; linarith)
  have a2 : isectApprox ⟨-1, 3 / 2⟩ (-ε) = true := happrox _ _ (by simp; linarith)
  have e1 : isectExact ⟨-1, -2⁻¹⟩ (-ε) = true := hexact _ _ (by simp; linarith)
  have e2 : isectExact ⟨-1, 3 / 2⟩ (-ε) = true := hexact _ _ (by simp; linarith)
  have e3 : isectExact ⟨1, 3 / 2⟩ (-ε) = false := hexact' _ _ (by simp; linarith)
  have e4 : isectExact ⟨1, 7 / 2⟩ (-ε) = false := hexact' _ _ (by simp; linarith)
  -- unfold, then the loop keeps the robustness of the last set, `[1, 7/2]`
  simp only [STL.robustnessReachSetGloballyCora, tp, Xp, ti, Xi]
  norm_num [hN, List.range_succ]
  have s1 : √((1 + ε) ^ 2) = 1 + ε := Real.sqrt_sq (by linarith)
  have n1 : (-1 + ε) ≠ 0 := by linarith
  have n2 : (1 + ε) ≠ 0 := by linarith
  simp [List.filter, m1, m2, m3, m4, m5, m6, m7, a1, a2, e1, e2, e3, e4, s1, n1, n2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
