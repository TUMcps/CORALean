module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeOfBounds
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorSetSuccSubset
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverTransformed
public import CORALean.Global.MulVecPosNegBounds
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The reachability-based estimator is tighter than the transformed interval observer

[1, Thm. 8]: with the same gain `L` and the observer Eq. 42 of [1, Thm. 5] started at the box of
[1, Alg. 1] at `k = 0`, `x̲ᵗ_k ≤ x̲_k` and `x̅_k ≤ x̅ᵗ_k`, provided `S` is invertible and
`R = S (A - LC) S⁻¹` elementwise nonnegative, the conditions of [1, Thm. 5] under which (42) is
defined and an interval observer; the theorem omits them and its proof uses them (its Eq. 71 is
Eq. 63 for the transformed system). By induction on Eq. 24 of [1, Thm. 2], `S e` lies between the
transformed bounds less `S x̂_k` for every reachable error `e` its Eq. 72, and [1, Lemma 2] at
`S⁻¹` bounds `e` itself its Eq. 78; the box of Alg. 1 is the hull of the reachable error.

## Inputs
* `sys` – system
* `L` – observer gain
* `S` – coordinate transformation
* `X₀` – initial zonotope
* `W` – disturbance zonotope
* `V` – noise zonotope
* `wl` – lower disturbance bound
* `wu` – upper disturbance bound
* `vl` – lower noise bound
* `vu` – upper noise bound
* `u` – inputs
* `y` – measurements
* `k` – step
* `i` – coordinate

## Hypotheses
* `hS` – transformation invertible
* `hR` – transformed error matrix nonnegative
* `hW` – disturbance zonotope within the bounds
* `hV` – noise zonotope within the bounds

## Conclusion
* the estimator's bounds are tighter than the transformed observer's

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control, 2019.
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

theorem LinearSysDT.intervalEstimate_le_intervalObserverTransformed (sys : LinearSysDT ℝ n)
    (L : Mat ℝ n sys.q)
    (S : Mat ℝ n n) (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ sys.r))
    (V : Zonotope (Vec ℝ sys.s)) (wl wu : Vec ℝ sys.r) (vl vu : Vec ℝ sys.s) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (hS : IsUnit S.det) (hR : ∀ i j, 0 ≤ (S * (sys.A - L * sys.C) * S⁻¹) i j)
    (hW : ∀ w ∈ W.construct, ∀ i, wl i ≤ w i ∧ w i ≤ wu i)
    (hV : ∀ v ∈ V.construct, ∀ i, vl i ≤ v i ∧ v i ≤ vu i) (k : ℕ) (i : Fin n) : -- --- CONCL ---
    let Alg := LinearSysDT.intervalEstimate sys L X₀ W V u y
    let Obs := LinearSysDT.intervalObserverTransformed sys L S wl wu vl vu (Alg 0).inf
      (Alg 0).sup u y
    (Obs k).inf i ≤ (Alg k).inf i ∧ (Alg k).sup i ≤ (Obs k).sup i := by -- --- PROOF ---
  intro Alg Obs
  set X := LinearSysDT.intervalEstimateState sys L X₀ W V u y
  set Z := LinearSysDT.intervalObserverCoord sys L S wl wu vl vu (Alg 0).inf (Alg 0).sup
    u y
  set R := S * (sys.A - L * sys.C) * S⁻¹
  set K := S * sys.E
  set G := -(S * L * sys.F)
  set gu := K.map (max 0) *ᵥ wu - (K.map (max 0) - K) *ᵥ wl + G.map (max 0) *ᵥ vu -
    (G.map (max 0) - G) *ᵥ vl
  set gl := K.map (max 0) *ᵥ wl - (K.map (max 0) - K) *ᵥ wu + G.map (max 0) *ᵥ vl -
    (G.map (max 0) - G) *ᵥ vu
  have hSS : S⁻¹ * S = 1 := nonsing_inv_mul S hS
  have hRS : R * S = S * (sys.A - L * sys.C) := by
    rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
  have hRSv : ∀ a : Vec ℝ n, R *ᵥ (S *ᵥ a) = (S * (sys.A - L * sys.C)) *ᵥ a := fun a => by
    rw [mulVec_mulVec, hRS]
  -- the estimate, transformed: `S x̂_{k+1} = R S x̂_k + SBu + SLy` its Eq. 64
  have hx : ∀ k, S *ᵥ (X (k + 1)).x = R *ᵥ (S *ᵥ (X k).x) + (S * sys.B) *ᵥ u k +
      (S * L) *ᵥ y k := fun k => by
    change S *ᵥ (LinearSysDT.intervalEstimateStep sys L (u k) (y k) (X k)).x = _
    rw [hRSv]
    simp only [LinearSysDT.intervalEstimateStep, sub_mulVec, mulVec_sub, mulVec_add,
      ← mulVec_mulVec, Matrix.mul_sub]
    abel
  have hup : ∀ k, (Z (k + 1)).sup - S *ᵥ (X (k + 1)).x =
      R *ᵥ ((Z k).sup - S *ᵥ (X k).x) + gu := fun k => by
    change R *ᵥ (Z k).sup + (S * sys.B) *ᵥ u k + (S * L) *ᵥ y k + gu - _ = _
    rw [hx, mulVec_sub]; abel
  have hlo : ∀ k, (Z (k + 1)).inf - S *ᵥ (X (k + 1)).x =
      R *ᵥ ((Z k).inf - S *ᵥ (X k).x) + gl := fun k => by
    change R *ᵥ (Z k).inf + (S * sys.B) *ᵥ u k + (S * L) *ᵥ y k + gl - _ = _
    rw [hx, mulVec_sub]; abel
  have hmono : ∀ a b : Vec ℝ n, (∀ j, a j ≤ b j) → ∀ j, (R *ᵥ a) j ≤ (R *ᵥ b) j :=
    fun a b h j => by
      simp only [mulVec, dotProduct]
      exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hR j l)
  -- its Eq. 72: `S e` lies between the transformed bounds less `S x̂`
  have hbd : ∀ k, ∀ e ∈ LinearSysDT.reachErrorSet sys L X₀ W V k, ∀ j,
      ((Z k).inf - S *ᵥ (X k).x) j ≤ (S *ᵥ e) j ∧
        (S *ᵥ e) j ≤ ((Z k).sup - S *ᵥ (X k).x) j := by
    intro k
    induction k with
    | zero =>
      intro e he j
      -- the initial box of Alg. 1 holds `x̂₀ + e`, and [1, Lemma 2] at `S`
      have h := (LinearSysDT.intervalEstimate_error_eq_hull sys L X₀ W V u y 0).1 he
      have hb := mulVec_posNeg_bounds S ((X 0).x + e) (Alg 0).inf (Alg 0).sup (fun l => by
        have hl := h l
        change ((X 0).Sx.interval.plus ((X 0).Sw.plus (X 0).Sv)).inf l ≤ e l ∧
          e l ≤ ((X 0).Sx.interval.plus ((X 0).Sw.plus (X 0).Sv)).sup l at hl
        change (X 0).x l + _ ≤ (X 0).x l + e l ∧ (X 0).x l + e l ≤ (X 0).x l + _
        constructor <;> linarith [hl.1, hl.2]) j
      rw [mulVec_add] at hb
      change ((S.map (max 0)) *ᵥ (Alg 0).inf - (S.map (max 0) - S) *ᵥ (Alg 0).sup -
          S *ᵥ (X 0).x) j ≤ _ ∧
        _ ≤ ((S.map (max 0)) *ᵥ (Alg 0).sup - (S.map (max 0) - S) *ᵥ (Alg 0).inf -
          S *ᵥ (X 0).x) j
      simp only [Pi.add_apply, Pi.sub_apply] at hb ⊢
      constructor <;> linarith [hb.1, hb.2]
    | succ k ih =>
      -- one step: `R ≥ 0` keeps the order, and Lemma 2 bounds the noise term
      intro e he j
      obtain ⟨_, ⟨_, ⟨e', he', rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩ :=
        LinearSysDT.reachErrorSet_succ_subset sys L X₀ W V k he
      have hK := mulVec_posNeg_bounds K w wl wu (hW w hw) j
      have hG := mulVec_posNeg_bounds G v vl vu (hV v hv) j
      have h1 := hmono _ _ (fun l => (ih e' he' l).1) j
      have h2 := hmono _ _ (fun l => (ih e' he' l).2) j
      -- `S e = R (S e') + S E w - S L F v`
      have hSe : S *ᵥ ((sys.A - L * sys.C) *ᵥ e' + sys.E *ᵥ w + -(L * sys.F) *ᵥ v) =
          R *ᵥ (S *ᵥ e') + (K *ᵥ w + G *ᵥ v) := by
        rw [hRSv]
        simp only [K, G, mulVec_add, mulVec_mulVec, neg_mulVec, mulVec_neg, Matrix.mul_assoc]
        abel
      rw [hup, hlo, hSe]
      simp only [Pi.add_apply, Pi.sub_apply, gu, gl] at hK hG h1 h2 ⊢
      constructor <;> linarith [hK.1, hK.2, hG.1, hG.2]
  cases k with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ k =>
    -- its Eq. 78: [1, Lemma 2] at `S⁻¹` bounds `e = S⁻¹ (S e)`
    set Tp := S⁻¹.map (max 0)
    set Tn := Tp - S⁻¹
    have hT : Tp - Tn = S⁻¹ := by simp [Tn]
    obtain ⟨h1, h2⟩ := LinearSysDT.intervalEstimate_le_of_bounds sys L X₀ W V u y (k + 1)
      (Tp *ᵥ ((Z (k + 1)).inf - S *ᵥ (X (k + 1)).x) - Tn *ᵥ ((Z (k + 1)).sup - S *ᵥ (X (k + 1)).x))
      (Tp *ᵥ ((Z (k + 1)).sup - S *ᵥ (X (k + 1)).x) - Tn *ᵥ ((Z (k + 1)).inf - S *ᵥ (X (k + 1)).x))
      (fun e he j => by
        have hb := mulVec_posNeg_bounds S⁻¹ (S *ᵥ e) _ _ (fun l => hbd (k + 1) e he l) j
        rwa [mulVec_mulVec, hSS, one_mulVec] at hb) i
    rw [show LinearSysDT.intervalEstimateState sys L X₀ W V u y (k + 1) = X (k + 1)
      from rfl] at h1 h2
    -- `x̂ = (S⁻¹)⁺ S x̂ - (S⁻¹)⁻ S x̂`
    have hxh := congrFun (show (Tp - Tn) *ᵥ (S *ᵥ (X (k + 1)).x) = (X (k + 1)).x by
      rw [hT, mulVec_mulVec, hSS, one_mulVec]) i
    simp only [sub_mulVec, mulVec_sub, Pi.sub_apply] at hxh h1 h2
    change (Tp *ᵥ (Z (k + 1)).inf - Tn *ᵥ (Z (k + 1)).sup) i ≤ _ ∧
      _ ≤ (Tp *ᵥ (Z (k + 1)).sup - Tn *ᵥ (Z (k + 1)).inf) i
    simp only [Pi.sub_apply]
    constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
