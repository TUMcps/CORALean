module

public import CORALean.ContSet.VPolytope.Float.Operations.IsFullDimWith
public import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# A `true` from `VPolytope.isFullDim` proves an interior point

Let `v̄` be the mean of the vertices. A point `y` within `B` of `v̄` gives the vector `(y - v̄, 0)`
of `n + 1` entries, which the checked right inverse of `[V; 1ᵀ]` writes as `[V; 1ᵀ] λ'` with
`|λ'ⱼ| ≤ δ` (`Zonotope.ballCert_reach`). The weights `1/k + λ'ⱼ` are nonnegative as `k δ ≤ 1`,
sum to one because the last row of the product is zero, and combine the vertices into
`v̄ + (y - v̄) = y`. So the open box of radius `B` around `v̄` lies in the nominal polytope, and
adding the error box's lower corner keeps an interior point (`subset_interior_add_left`).

## Inputs
* `P` – polytope
* `H` – proposed right inverse

## Hypotheses
* `h` – `isFullDimWith` returns `true`

## Conclusion
* `P` has nonempty interior
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A vector reached by the bordered matrix has weights summing to zero and the vertex rows
reached: the last row is the sum of the weights. -/
theorem VPolytope.aux_weights (P : VPolytope (Vec 𝕋 n)) (z : Vec ℝ n) (w : Vec ℝ P.k)
    (h : toRealMat P.bordered *ᵥ w = fun i => if hi : i.val < n then z ⟨i.val, hi⟩ else 0)
    : -- --- CONCL ---
    ∑ j, w j = 0 ∧ ∀ i : Fin n, ∑ j, toReal (P.V j i) * w j = z i := by -- --- PROOF ---
  refine ⟨?_, fun i => ?_⟩
  · have := congrFun h (Fin.last n)
    simp only [Matrix.mulVec, dotProduct, Fin.val_last, lt_irrefl, dite_false] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by
      simp [toRealMat, VPolytope.bordered, toReal_one]
  · have := congrFun h (Fin.castSucc i)
    simp only [Matrix.mulVec, dotProduct, Fin.val_castSucc, i.isLt, dite_true] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by
      simp [toRealMat, VPolytope.bordered]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.isFullDim_sound {P : VPolytope (Vec 𝕋 n)} {H : Mat 𝕋 P.k (n + 1)}
    (h : P.isFullDimWith H = true) : -- --- CONCL ---
    (interior P.construct).Nonempty := by -- --- PROOF ---
  simp only [VPolytope.isFullDimWith, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨hk, hkδ⟩, hc⟩, hE⟩ := h
  obtain ⟨hB, hreach⟩ := Zonotope.ballCert_reach hc
  have hkpos : (0 : ℝ) < P.k := by exact_mod_cast hk
  -- the coefficient bound `δ` is at most `1 / k`
  obtain ⟨δ, hδ⟩ : ∃ δ : 𝕋, δ = half (divDown (one : 𝕋) (nsmulUp P.k one)) := ⟨_, rfl⟩
  rw [← hδ] at hkδ hc hB hreach
  have hδk : toReal δ ≤ 1 / (P.k : ℝ) := by
    have := le_trans (le_nsmulUp P.k δ) (toReal_le_of_le hkδ)
    rw [toReal_one] at this
    rw [le_div_iff₀ hkpos]
    linarith
  -- the mean of the vertices, and the open box around it
  obtain ⟨m, hm⟩ : ∃ m : Vec ℝ n, ∀ i, m i = (1 / (P.k : ℝ)) * ∑ j, toReal (P.V j i) :=
    ⟨fun i => (1 / (P.k : ℝ)) * ∑ j, toReal (P.V j i), fun _ => rfl⟩
  let U : Set (Vec ℝ n) := Set.pi Set.univ fun i =>
    Metric.ball (m i) (toReal (Zonotope.ballB H δ))
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hUsub : U ⊆ nominalSet P := fun y hy => by
    -- the vector `(y - m, 0)` is reached by weights `λ'`, none larger than `δ`
    obtain ⟨w, hw, hwδ⟩ := hreach
      (fun i => if hi : i.val < n then y ⟨i.val, hi⟩ - m ⟨i.val, hi⟩ else 0) (fun i => by
        by_cases hi : i.val < n
        · have := hy ⟨i.val, hi⟩ (Set.mem_univ _)
          rw [Metric.mem_ball, Real.dist_eq] at this
          simpa [hi] using this.le
        · simpa [hi] using hB.le)
    obtain ⟨hsum, hrows⟩ := VPolytope.aux_weights P (fun i => y i - m i) w hw
    -- the weights `1/k + w j`: nonnegative, summing to one, combining to `y`
    change ∃ β : Fin P.k → ℝ, (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1
      ∧ y = ∑ j, β j • (fun i : Fin n => toReal (P.V j i))
    refine ⟨fun j => 1 / (P.k : ℝ) + w j, fun j => ?_, ?_, ?_⟩
    · have := (abs_le.mp (hwδ j)).1
      linarith
    · rw [Finset.sum_add_distrib, hsum]
      simp [Finset.sum_const, hkpos.ne']
    · -- the vertex rows combine to `y`
      funext i
      have hi := hrows i
      have : ∑ j, (1 / (P.k : ℝ) + w j) * toReal (P.V j i) = y i := by
        calc ∑ j, (1 / (P.k : ℝ) + w j) * toReal (P.V j i)
            = (1 / (P.k : ℝ)) * ∑ j, toReal (P.V j i) + ∑ j, toReal (P.V j i) * w j := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = y i := by rw [← hm i, hi]; ring
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact this.symm
  have hx : m ∈ interior (nominalSet P) :=
    interior_maximal hUsub hU fun i _ => by simpa [Metric.mem_ball] using hB
  have he : (fun i => toReal (P.I_error.inf i)) ∈ (I_error P).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
