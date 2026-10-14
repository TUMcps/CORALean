module

public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverTransformed
public import CORALean.Global.MulVecPosNegBounds
public import CORALean.Global.NonnegOfNonnegRecurrence
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The interval observer based on a coordinate transformation holds the true state

[1, Thm. 5]: for an invertible `S` with `R = S (A - LC) S⁻¹` elementwise nonnegative and
`x̲ᵗ₀ ≤ x_0 ≤ x̅ᵗ₀`, the bounds of its Eq. 42 hold `x_k` for every `k`, for every run of
`x_{k+1} = A x_k + B u_k + E w_k`, `y_k = C x_k + F v_k` with `w̲ ≤ w_k ≤ w̅`, `v̲ ≤ v_k ≤ v̅`.
As in the paper: `z_k = S x_k` follows `z_{k+1} = R z_k + SBu_k + SLy_k + SEw_k - SLFv_k` (its
Eq. 44), so the errors of (42c), (42d) stay nonnegative (its Eq. 47, [1, Lemma 2],
[1, Lemma 3]), and `x_k = S⁻¹ z_k` is bounded by (42e), (42f) [1, Lemma 2]. That `A - LC` is
Schur is not needed for the enclosure, only for the bounds to stay bounded.

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

theorem LinearSysDT.intervalObserverTransformed_outer (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (S : Mat ℝ n n)
    (wl wu : Vec ℝ sys.r) (vl vu : Vec ℝ sys.s) (xl₀ xu₀ : Vec ℝ n) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (x : ℕ → Vec ℝ n) (w : ℕ → Vec ℝ sys.r) (v : ℕ → Vec ℝ sys.s)
    (hS : IsUnit S.det) (hR : ∀ i j, 0 ≤ (S * (sys.A - L * sys.C) * S⁻¹) i j)
    (h0 : ∀ i, xl₀ i ≤ x 0 i ∧ x 0 i ≤ xu₀ i) (hw : ∀ k i, wl i ≤ w k i ∧ w k i ≤ wu i)
    (hv : ∀ k i, vl i ≤ v k i ∧ v k i ≤ vu i)
    (hstep : ∀ k, x (k + 1) = sys.A *ᵥ x k + sys.B *ᵥ u k + sys.E *ᵥ w k)
    (hy : ∀ k, y k = sys.C *ᵥ x k + sys.F *ᵥ v k) (k : ℕ) :
    x k ∈ (LinearSysDT.intervalObserverTransformed sys L S wl wu vl vu xl₀ xu₀ u y
      k).construct := by -- --- PROOF ---
  set Z := LinearSysDT.intervalObserverCoord sys L S wl wu vl vu xl₀ xu₀ u y
  set R := S * (sys.A - L * sys.C) * S⁻¹
  set K := S * sys.E
  set G := -(S * L * sys.F)
  set gu := K.map (max 0) *ᵥ wu - (K.map (max 0) - K) *ᵥ wl + G.map (max 0) *ᵥ vu -
    (G.map (max 0) - G) *ᵥ vl
  set gl := K.map (max 0) *ᵥ wl - (K.map (max 0) - K) *ᵥ wu + G.map (max 0) *ᵥ vl -
    (G.map (max 0) - G) *ᵥ vu
  have hSS : S⁻¹ * S = 1 := nonsing_inv_mul S hS
  -- its Eq. 44: the transformed state
  have hz : ∀ k, S *ᵥ x (k + 1) = R *ᵥ (S *ᵥ x k) + (S * sys.B) *ᵥ u k + (S * L) *ᵥ y k +
      (K *ᵥ w k + G *ᵥ v k) := fun k => by
    have hRS : R *ᵥ (S *ᵥ x k) = (S * (sys.A - L * sys.C)) *ᵥ x k := by
      rw [mulVec_mulVec, Matrix.mul_assoc (S * (sys.A - L * sys.C)), hSS, Matrix.mul_one]
    rw [hRS, hstep, hy]
    simp only [K, G, sub_mulVec, mulVec_add, neg_mulVec, ← mulVec_mulVec,
      Matrix.mul_sub]
    abel
  -- the disturbance term between `g̲` and `g̅` [1, Lemma 2]
  have hg : ∀ k i, gl i ≤ (K *ᵥ w k + G *ᵥ v k) i ∧ (K *ᵥ w k + G *ᵥ v k) i ≤ gu i := by
    intro k i
    have hK := mulVec_posNeg_bounds K (w k) wl wu (hw k) i
    have hG := mulVec_posNeg_bounds G (v k) vl vu (hv k) i
    simp only [gu, gl, Pi.add_apply, Pi.sub_apply] at hK hG ⊢
    constructor <;> linarith [hK.1, hK.2, hG.1, hG.2]
  -- its Eq. 47, [1, Lemma 3]: the transformed errors stay nonnegative
  have h0z := fun i => mulVec_posNeg_bounds S (x 0) xl₀ xu₀ h0 i
  have hU := nonneg_of_nonneg_recurrence R (fun k => (Z k).sup - S *ᵥ x k)
    (fun k => gu - (K *ᵥ w k + G *ᵥ v k)) hR
    (fun k i => by simp only [Pi.sub_apply]; linarith [(hg k i).2])
    (fun i => by simp only [Pi.sub_apply]; exact sub_nonneg.mpr (h0z i).2)
    (fun k => by
      change R *ᵥ (Z k).sup + (S * sys.B) *ᵥ u k + (S * L) *ᵥ y k + gu - S *ᵥ x (k + 1) = _
      rw [hz, mulVec_sub]; abel)
  have hL := nonneg_of_nonneg_recurrence R (fun k => S *ᵥ x k - (Z k).inf)
    (fun k => (K *ᵥ w k + G *ᵥ v k) - gl) hR
    (fun k i => by simp only [Pi.sub_apply]; linarith [(hg k i).1])
    (fun i => by simp only [Pi.sub_apply]; exact sub_nonneg.mpr (h0z i).1)
    (fun k => by
      change S *ᵥ x (k + 1) - (R *ᵥ (Z k).inf + (S * sys.B) *ᵥ u k + (S * L) *ᵥ y k + gl) = _
      rw [hz, mulVec_sub]; abel)
  cases k with
  | zero => exact h0
  | succ k =>
    -- [1, Lemma 2] at `S⁻¹`, `x = S⁻¹ (S x)`
    intro i
    have hb := mulVec_posNeg_bounds S⁻¹ (S *ᵥ x (k + 1)) (Z (k + 1)).inf (Z (k + 1)).sup
      (fun j => by
        have h1 := hU (k + 1) j
        have h2 := hL (k + 1) j
        simp only [Pi.sub_apply] at h1 h2
        exact ⟨by linarith, by linarith⟩) i
    rw [mulVec_mulVec, hSS, one_mulVec] at hb
    exact hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
