module

public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserver
public import CORALean.Global.MulVecPosNegBounds
public import CORALean.Global.NonnegOfNonnegRecurrence
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The interval observer holds the true state

[1, Thm. 4]: if `A - LC` is elementwise nonnegative and `x̲₀ ≤ x_0 ≤ x̅₀`, the bounds of the
interval observer [1, Eq. 36] and [1, Eq. 37] hold `x_k` for every `k`, for every run of
`x_{k+1} = A x_k + B u_k + E w_k`, `y_k = C x_k + F v_k` with `w̲ ≤ w_k ≤ w̅`, `v̲ ≤ v_k ≤ v̅`.
As in the paper: the errors `x̅_k - x_k` and `x_k - x̲_k` follow `e_{k+1} = (A - LC) e_k + δ_k`
with `δ_k ≥ 0` by [1, Lemma 2] (`mulVec_posNeg_bounds`), and stay nonnegative by [1, Lemma 3]
(`nonneg_of_nonneg_recurrence`).

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

open Matrix CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intervalObserver_outer (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (wl wu : Vec ℝ sys.r) (vl vu : Vec ℝ sys.s)
    (xl₀ xu₀ : Vec ℝ n) (u : ℕ → Vec ℝ sys.m) (y : ℕ → Vec ℝ sys.q) (x : ℕ → Vec ℝ n)
    (w : ℕ → Vec ℝ sys.r) (v : ℕ → Vec ℝ sys.s) (hM : ∀ i j, 0 ≤ (sys.A - L * sys.C) i j)
    (h0 : ∀ i, xl₀ i ≤ x 0 i ∧ x 0 i ≤ xu₀ i) (hw : ∀ k i, wl i ≤ w k i ∧ w k i ≤ wu i)
    (hv : ∀ k i, vl i ≤ v k i ∧ v k i ≤ vu i)
    (hstep : ∀ k, x (k + 1) = sys.A *ᵥ x k + sys.B *ᵥ u k + sys.E *ᵥ w k)
    (hy : ∀ k, y k = sys.C *ᵥ x k + sys.F *ᵥ v k) (k : ℕ) :
    x k ∈ (LinearSysDT.intervalObserver sys L wl wu vl vu xl₀ xu₀ u y
      k).construct := by -- --- PROOF ---
  set I := LinearSysDT.intervalObserver sys L wl wu vl vu xl₀ xu₀ u y
  set G := -(L * sys.F)
  set du := sys.E.map (max 0) *ᵥ wu - (sys.E.map (max 0) - sys.E) *ᵥ wl + G.map (max 0) *ᵥ vu -
    (G.map (max 0) - G) *ᵥ vl
  set dl := sys.E.map (max 0) *ᵥ wl - (sys.E.map (max 0) - sys.E) *ᵥ wu + G.map (max 0) *ᵥ vl -
    (G.map (max 0) - G) *ᵥ vu
  -- its Eq. 40: the disturbance term lies between `d̲` and `d̅`, by [1, Lemma 2]
  have hd : ∀ k i, dl i ≤ (sys.E *ᵥ w k + G *ᵥ v k) i ∧ (sys.E *ᵥ w k + G *ᵥ v k) i ≤ du i := by
    intro k i
    have hE := mulVec_posNeg_bounds sys.E (w k) wl wu (hw k) i
    have hG := mulVec_posNeg_bounds G (v k) vl vu (hv k) i
    simp only [Pi.add_apply, Pi.sub_apply] at hE hG ⊢
    simp only [du, dl, Pi.add_apply, Pi.sub_apply]
    constructor <;> linarith [hE.1, hE.2, hG.1, hG.2]
  -- the error recursions
  have hrec : ∀ k, x (k + 1) = (sys.A - L * sys.C) *ᵥ x k + sys.B *ᵥ u k + L *ᵥ y k +
      (sys.E *ᵥ w k + G *ᵥ v k) := fun k => by
    rw [hstep, hy]
    simp only [G, sub_mulVec, mulVec_add, neg_mulVec, ← mulVec_mulVec]
    abel
  have hup : ∀ k, (I (k + 1)).sup =
      (sys.A - L * sys.C) *ᵥ (I k).sup + sys.B *ᵥ u k + L *ᵥ y k + du :=
    fun k => by
      show sys.A *ᵥ (I k).sup + sys.B *ᵥ u k + L *ᵥ (y k - sys.C *ᵥ (I k).sup) + du = _
      simp only [sub_mulVec, mulVec_sub, ← mulVec_mulVec]
      abel
  have hlo : ∀ k, (I (k + 1)).inf =
      (sys.A - L * sys.C) *ᵥ (I k).inf + sys.B *ᵥ u k + L *ᵥ y k + dl :=
    fun k => by
      show sys.A *ᵥ (I k).inf + sys.B *ᵥ u k + L *ᵥ (y k - sys.C *ᵥ (I k).inf) + dl = _
      simp only [sub_mulVec, mulVec_sub, ← mulVec_mulVec]
      abel
  -- [1, Lemma 3] on `x̅ - x` and `x - x̲`
  have hU := nonneg_of_nonneg_recurrence (sys.A - L * sys.C) (fun k => (I k).sup - x k)
    (fun k => du - (sys.E *ᵥ w k + G *ᵥ v k)) hM (fun k i => by
      simp only [Pi.sub_apply]; linarith [(hd k i).2])
    (fun i => by simp only [Pi.sub_apply]; exact sub_nonneg.mpr (h0 i).2)
    (fun k => by rw [hup, hrec, mulVec_sub]; abel) k
  have hL := nonneg_of_nonneg_recurrence (sys.A - L * sys.C) (fun k => x k - (I k).inf)
    (fun k => (sys.E *ᵥ w k + G *ᵥ v k) - dl) hM (fun k i => by
      simp only [Pi.sub_apply]; linarith [(hd k i).1])
    (fun i => by simp only [Pi.sub_apply]; exact sub_nonneg.mpr (h0 i).1)
    (fun k => by rw [hlo, hrec, mulVec_sub]; abel) k
  intro i
  change (I k).inf i ≤ x k i ∧ x k i ≤ (I k).sup i
  have h1 := hU i
  have h2 := hL i
  simp only [Pi.sub_apply] at h1 h2
  exact ⟨by linarith, by linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
