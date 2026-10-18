module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeOfBounds
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorSetSuccSubset
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserver
public import CORALean.Global.MulVecPosNegBounds
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The reachability-based estimator is tighter than the interval observer

[1, Thm. 7]: with the same gain `L` and the interval observer [1, Eq. 36] started at the box of
[1, Alg. 1] at `k = 0`, `x̲ⁱ_k ≤ x̲_k` and `x̅_k ≤ x̅ⁱ_k`, provided `A - LC` is elementwise
nonnegative, which the theorem omits; it is the condition under which (36) is an interval
observer [1, Thm. 4] and the proof uses it (Lemma 5 at `A - LC`). `W` and `V` lie in the boxes
`[w̲, w̅]`, `[v̲, v̅]` of (37). By induction on Eq. 24 of [1, Thm. 2] every reachable error lies
between the observer's bounds less `x̂_k`, the upper one following `ē_{k+1} = (A - LC) ē_k + d̅`
(its Eq. 57); the box of Alg. 1 is the hull of the reachable error.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intervalEstimate_le_intervalObserver (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ sys.r)) (V : Zonotope (Vec ℝ sys.s))
    (wl wu : Vec ℝ sys.r) (vl vu : Vec ℝ sys.s) (u : ℕ → Vec ℝ sys.m) (y : ℕ → Vec ℝ sys.q)
    (hM : ∀ i j, 0 ≤ (sys.A - L * sys.C) i j) (hW : ∀ w ∈ W.construct, ∀ i, wl i ≤ w i ∧ w i ≤ wu i)
    (hV : ∀ v ∈ V.construct, ∀ i, vl i ≤ v i ∧ v i ≤ vu i) (k : ℕ) (i : Fin n) : -- --- STMT ---
    let Alg := LinearSysDT.intervalEstimate sys L X₀ W V u y
    let Obs := LinearSysDT.intervalObserver sys L wl wu vl vu (Alg 0).inf (Alg 0).sup u y
    (Obs k).inf i ≤ (Alg k).inf i ∧ (Alg k).sup i ≤ (Obs k).sup i := by -- --- PROOF ---
  intro Alg Obs
  set S := LinearSysDT.intervalEstimateState sys L X₀ W V u y
  set M := sys.A - L * sys.C
  set G := -(L * sys.F)
  set du := sys.E.map (max 0) *ᵥ wu - (sys.E.map (max 0) - sys.E) *ᵥ wl + G.map (max 0) *ᵥ vu -
    (G.map (max 0) - G) *ᵥ vl
  set dl := sys.E.map (max 0) *ᵥ wl - (sys.E.map (max 0) - sys.E) *ᵥ wu + G.map (max 0) *ᵥ vl -
    (G.map (max 0) - G) *ᵥ vu
  -- the observer's bounds less the estimate follow `(A - LC) ē + d̅` its Eq. 57
  have hx : ∀ k, (S (k + 1)).x = M *ᵥ (S k).x + sys.B *ᵥ u k + L *ᵥ y k := fun k => by
    change (LinearSysDT.intervalEstimateStep sys L (u k) (y k) (S k)).x = _
    simp only [LinearSysDT.intervalEstimateStep, M, sub_mulVec, mulVec_sub, ← mulVec_mulVec]
    abel
  have hup : ∀ k, (Obs (k + 1)).sup - (S (k + 1)).x = M *ᵥ ((Obs k).sup - (S k).x) + du :=
    fun k => by
      change sys.A *ᵥ (Obs k).sup + sys.B *ᵥ u k + L *ᵥ (y k - sys.C *ᵥ (Obs k).sup) + du - _ = _
      rw [hx]
      simp only [M, sub_mulVec, mulVec_sub, ← mulVec_mulVec]
      abel
  have hlo : ∀ k, (Obs (k + 1)).inf - (S (k + 1)).x = M *ᵥ ((Obs k).inf - (S k).x) + dl :=
    fun k => by
      change sys.A *ᵥ (Obs k).inf + sys.B *ᵥ u k + L *ᵥ (y k - sys.C *ᵥ (Obs k).inf) + dl - _ = _
      rw [hx]
      simp only [M, sub_mulVec, mulVec_sub, ← mulVec_mulVec]
      abel
  -- a nonnegative matrix keeps the order
  have hmono : ∀ a b : Vec ℝ n, (∀ j, a j ≤ b j) → ∀ j, (M *ᵥ a) j ≤ (M *ᵥ b) j :=
    fun a b h j => by
      simp only [mulVec, dotProduct]
      exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hM j l)
  -- every reachable error lies between the shifted bounds
  have hbd : ∀ k, ∀ e ∈ LinearSysDT.reachErrorSet sys L X₀ W V k, ∀ j,
      ((Obs k).inf - (S k).x) j ≤ e j ∧ e j ≤ ((Obs k).sup - (S k).x) j := by
    intro k
    induction k with
    | zero =>
      -- the observer starts at the box of Alg. 1, which holds `Ω_0`
      intro e he j
      have h := (LinearSysDT.intervalEstimate_error_eq_hull sys L X₀ W V u y 0).1 he j
      change ((S 0).Sx.interval.plus ((S 0).Sw.plus (S 0).Sv)).inf j ≤ e j ∧
        e j ≤ ((S 0).Sx.interval.plus ((S 0).Sw.plus (S 0).Sv)).sup j at h
      simp only [Pi.sub_apply]
      change (S 0).x j + _ - (S 0).x j ≤ e j ∧ e j ≤ (S 0).x j + _ - (S 0).x j
      constructor <;> linarith [h.1, h.2]
    | succ k ih =>
      -- one step: `A - LC ≥ 0` keeps the order, and Lemma 2 bounds the noise term
      intro e he j
      obtain ⟨_, ⟨_, ⟨e', he', rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩ :=
        LinearSysDT.reachErrorSet_succ_subset sys L X₀ W V k he
      have hE := mulVec_posNeg_bounds sys.E w wl wu (hW w hw) j
      have hG := mulVec_posNeg_bounds G v vl vu (hV v hv) j
      have h1 := hmono _ _ (fun l => (ih e' he' l).1) j
      have h2 := hmono _ _ (fun l => (ih e' he' l).2) j
      rw [hup, hlo]
      simp only [Pi.add_apply, Pi.sub_apply, du, dl] at hE hG h1 h2 ⊢
      constructor <;> linarith [hE.1, hE.2, hG.1, hG.2]
  -- the box of Alg. 1 is the hull of the reachable error
  obtain ⟨h1, h2⟩ := LinearSysDT.intervalEstimate_le_of_bounds sys L X₀ W V u y k
    ((Obs k).inf - (S k).x) ((Obs k).sup - (S k).x) (hbd k) i
  rw [show LinearSysDT.intervalEstimateState sys L X₀ W V u y k = S k from rfl] at h1 h2
  simp only [Pi.sub_apply, add_sub_cancel] at h1 h2
  exact ⟨h1, h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
