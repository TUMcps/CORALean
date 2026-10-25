module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# A dual certificate for the semidefinite relaxations of the containment radius

The duality step of [1, Thm. 17] and [1, Thm. 19], taken there from Kulmburg's "The Generalized
Matrix Norm Problem". The relaxations minimize `½ (‖v‖_{s₁} + ‖w‖_{s₂})` over the `(v, w)` with
`[Diag(v), 0; 0, H Diag(w) Hᵀ] ≼ [0, Gᵀ; G, 0]` (Eq. 39, Eq. 42). If every such pair has objective
above `t > 0` and `H` is onto, some `X ≽ 0` has `‖diag X₁₁‖_{s₁*} ≤ 1`,
`‖diag(Hᵀ X₂₂ H)‖_{s₂*} ≤ 1` and `Σ G_{kj} X_{(n,k),(m,j)} ≥ t`. Proved by separating the convex
set of slack matrices at objective `≤ t` from the open cone of uniformly positive definite ones
(`geometric_hahn_banach_open`); the separator `-f = ⟨W, ·⟩` gives `X = (t / a) J W J`.

## Inputs
* `s₁` – exponent of the first norm
* `s₁'` – its conjugate exponent
* `s₂` – exponent of the second norm
* `s₂'` – its conjugate exponent
* `G` – coupling matrix
* `H` – generator matrix of the second block
* `t` – objective level

## Hypotheses
* `hH` – the generator matrix is onto
* `ht` – the level is positive
* `hK` – every feasible pair has objective above the level

## Conclusion
* a positive semidefinite matrix with dual-norm-bounded diagonals pairs with the coupling to `t`

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal NNReal
open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `xᵀ X x` as a double sum. -/
theorem aux_dbs_quad {ι : Type*} [Fintype ι] (X : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (X *ᵥ x) = ∑ i, ∑ j, x i * X i j * x j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A positive semidefinite real matrix has `|Xᵢⱼ| ≤ (Xᵢᵢ + Xⱼⱼ) / 2`. -/
theorem aux_dbs_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℝ}
    (hX : X.PosSemidef) (i j : ι) : -- --- CONCL ---
    |X i j| ≤ (X i i + X j j) / 2 := by -- --- PROOF ---
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg hX.diag_nonneg]; linarith
  have hsym : X j i = X i j := by
    have := hX.isHermitian.apply i j
    simpa using this
  have hq : ∀ s : ℝ, 0 ≤ X i i + (s * X j i + (X i j * s + s * X j j * s)) := fun s => by
    have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j s)
    simp only [star_trivial] at h
    rw [aux_dbs_quad] at h
    simp only [Pi.add_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib] at h
    simpa [ite_mul, mul_ite, Finset.sum_ite_eq', hij, Ne.symm hij, add_assoc] using h
  have h1 := hq 1
  have h2 := hq (-1)
  rw [abs_le]; constructor <;> nlinarith

/-- A continuous linear functional on matrices is `X ↦ Σ Xᵢⱼ f(Eᵢⱼ)`. -/
theorem aux_dbs_functional {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Matrix ι ι ℝ →L[ℝ] ℝ) (X : Matrix ι ι ℝ) : -- --- CONCL ---
    f X = ∑ i, ∑ j, X i j * f (single i j 1) := by -- --- PROOF ---
  conv_lhs => rw [matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single i j (X i j) = X i j • single i j (1 : ℝ) by
    rw [smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

/-- The uniformly positive definite matrices form an open set. -/
theorem aux_dbs_isOpen {ι : Type*} [Fintype ι] : -- --- CONCL ---
    IsOpen {X : Matrix ι ι ℝ |
      ∃ δ > 0, ∀ x : ι → ℝ, δ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (X *ᵥ x)} := by -- --- PROOF ---
  rw [isOpen_iff_forall_mem_open]
  -- a uniform `δ` at `X` survives an entrywise perturbation below `r`
  rintro X ⟨δ, hδ, hX⟩
  set c : ℝ := (Fintype.card ι : ℝ)
  set r : ℝ := δ / (2 * c + 1) with hr
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hrpos : 0 < r := div_pos hδ (by positivity)
  have hrc : r * c ≤ δ / 2 := by
    rw [hr, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  refine ⟨{Y | ∀ i j, |Y i j - X i j| < r}, fun Y hY => ⟨δ / 2, half_pos hδ, fun x => ?_⟩,
    ?_, fun i j => by simpa using hrpos⟩
  · have hxx : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    -- `|xᵀ (Y - X) x| ≤ r Σᵢⱼ (xᵢ² + xⱼ²)/2 = r c xᵀx ≤ δ/2 xᵀx`
    have hdiff : x ⬝ᵥ (X *ᵥ x) - x ⬝ᵥ (Y *ᵥ x) ≤ (δ / 2) * (x ⬝ᵥ x) := by
      rw [aux_dbs_quad, aux_dbs_quad, ← Finset.sum_sub_distrib]
      have hb : ∀ i j,
          x i * X i j * x j - x i * Y i j * x j ≤ r * ((x i * x i + x j * x j) / 2) :=
        fun i j => by
          have h := hY i j
          have hxy : |x i * x j| ≤ (x i * x i + x j * x j) / 2 := by
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + x j), sq_nonneg (x i - x j)]
          have : x i * X i j * x j - x i * Y i j * x j = -((Y i j - X i j) * (x i * x j)) := by
            ring
          rw [this]
          have h3 : |(Y i j - X i j) * (x i * x j)| ≤ r * ((x i * x i + x j * x j) / 2) := by
            rw [abs_mul]
            exact mul_le_mul h.le hxy (abs_nonneg _) hrpos.le
          linarith [neg_abs_le ((Y i j - X i j) * (x i * x j))]
      -- summed over the entries
      calc ∑ i, (∑ j, x i * X i j * x j - ∑ j, x i * Y i j * x j)
          = ∑ i, ∑ j, (x i * X i j * x j - x i * Y i j * x j) := by
            simp only [Finset.sum_sub_distrib]
        _ ≤ ∑ i, ∑ j, r * ((x i * x i + x j * x j) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
        _ = r * c * (x ⬝ᵥ x) := by
            simp only [dotProduct, add_div, mul_add, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div, c]
            ring
        _ ≤ (δ / 2) * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_right hrc hxx
    linarith [hX x]
  -- the neighbourhood is a finite intersection of open slabs
  · have : {Y : Matrix ι ι ℝ | ∀ i j, |Y i j - X i j| < r} =
        ⋂ i, ⋂ j, {Y | |Y i j - X i j| < r} := by
      ext Y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (by fun_prop) continuous_const

/-- The converse of Hölder for `u ≥ 0`: `Σ wᵢ uᵢ ≤ ‖w‖_s` for every `w ≥ 0` gives
`‖u‖_{s*} ≤ 1`. -/
theorem aux_dbs_dual_le_one (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (u : Fin l → ℝ) (hu : ∀ i, 0 ≤ u i)
    (h : ∀ w : Fin l → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i * u i ≤ ‖WithLp.toLp q w‖) : -- --- CONCL ---
    ‖WithLp.toLp q' u‖ ≤ 1 := by -- --- PROOF ---
  -- `q = ∞`: test with `w = 1`
  by_cases hq : q = ∞
  · have hq' : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q q').mp hq
    subst hq hq'
    have h1 := h 1 (fun _ => zero_le_one)
    simp only [Pi.one_apply, one_mul, PiLp.norm_toLp] at h1
    rw [PiLp.norm_eq_of_L1]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hu _)]
    exact h1.trans ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp)
  -- `q = 1`: test with the unit vectors
  by_cases hq1 : q = 1
  · have hq' : q' = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q' q).mpr hq1
    subst hq1 hq'
    rw [PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    have h1 := h (Pi.single i 1) (fun j => by by_cases hj : j = i <;> simp [hj])
    have hs : ‖WithLp.toLp 1 (Pi.single (M := fun _ : Fin l => ℝ) i 1)‖ = 1 := by
      rw [PiLp.norm_eq_of_L1]
      simp [Pi.single_apply, apply_ite]
    rw [hs] at h1
    simpa [Pi.single_apply, Real.norm_eq_abs, abs_of_nonneg (hu i)] using h1
  -- `1 < q < ∞`: the maximizer of `NNReal.isGreatest_Lp`
  · have hq'1 : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1
    have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hq'0 : 0 < q'.toReal :=
      ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hq'1
    have hR : q'.toReal.HolderConjugate q.toReal := by
      simpa using ENNReal.HolderTriple.toReal 1 hq'0 hq0
    obtain ⟨g, hg, hgeq⟩ := (NNReal.isGreatest_Lp Finset.univ (fun i => (u i).toNNReal) hR).1
    simp only [Set.mem_setOf_eq] at hg
    have h1 := h (fun i => g i) (fun i => (g i).2)
    have hL : (∑ i, ‖u i‖ ^ q'.toReal) ^ (1 / q'.toReal) = ∑ i, (g i : ℝ) * u i := by
      have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hgeq
      push_cast [Real.coe_toNNReal _ (hu _)] at this
      simp only [Real.norm_eq_abs, abs_of_nonneg (hu _)]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    -- `‖u‖_{q*} = Σ gᵢ uᵢ ≤ ‖g‖_q ≤ 1`
    rw [PiLp.norm_eq_sum hq'0, hL]
    refine h1.trans ?_
    rw [PiLp.norm_eq_sum hq0]
    refine Real.rpow_le_one (Finset.sum_nonneg fun i _ => by positivity) ?_ (by positivity)
    have := NNReal.coe_le_coe.mpr hg
    push_cast at this
    simpa [Real.norm_eq_abs] using this

/-- A bound `Σ vⱼ dⱼ ≤ 2a` on the ball `‖v‖_s ≤ 2t`, `d ≥ 0`, bounds `‖(t/a) d‖_{s*}` by `1`. -/
theorem aux_dbs_scaled_dual_le_one (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (d : Fin l → ℝ) (hd : ∀ i, 0 ≤ d i) {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (h : ∀ v : Fin l → ℝ, ‖WithLp.toLp q v‖ ≤ 2 * t → ∑ i, v i * d i ≤ 2 * a) : -- --- CONCL ---
    ‖WithLp.toLp q' (fun i => t / a * d i)‖ ≤ 1 := by -- --- PROOF ---
  refine aux_dbs_dual_le_one q q' _ (fun i => by have := hd i; positivity) fun w hw => ?_
  -- scale `w` onto the sphere of radius `2t`
  rcases (norm_nonneg (WithLp.toLp q w)).lt_or_eq with hpos | hzero
  · set c := 2 * t / ‖WithLp.toLp q w‖
    have hc : 0 < c := by positivity
    have hv := h (c • w) (by
      rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      simp only [c]
      rw [div_mul_cancel₀ _ hpos.ne'])
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at hv
    have : ∑ i, w i * d i ≤ a / t * ‖WithLp.toLp q w‖ := by
      calc ∑ i, w i * d i ≤ 2 * a / c := (le_div_iff₀' hc).mpr hv
        _ = a / t * ‖WithLp.toLp q w‖ := by simp only [c]; field_simp
    calc ∑ i, w i * (t / a * d i) = t / a * ∑ i, w i * d i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ t / a * (a / t * ‖WithLp.toLp q w‖) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ‖WithLp.toLp q w‖ := by field_simp
  -- `w = 0`
  · have hw0 : w = 0 := by
      have := norm_eq_zero.mp hzero.symm
      simpa using congrArg WithLp.ofLp this
    simp [hw0]

/-- A bound `Σ vⱼ dⱼ ≤ 0` near `v = 0`, `d ≥ 0`, forces `d = 0`. -/
theorem aux_dbs_eq_zero (q : ℝ≥0∞) [Fact (1 ≤ q)] (d : Fin l → ℝ) (hd : ∀ i, 0 ≤ d i) {t : ℝ}
    (ht : 0 < t)
    (h : ∀ v : Fin l → ℝ, ‖WithLp.toLp q v‖ ≤ 2 * t → ∑ i, v i * d i ≤ 0)
    (i : Fin l) : -- --- CONCL ---
    d i = 0 := by -- --- PROOF ---
  set e : Fin l → ℝ := Pi.single i 1
  set c := 2 * t / (‖WithLp.toLp q e‖ + 1)
  have hc : 0 < c := by positivity
  have hv := h (c • e) (by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    simp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (WithLp.toLp q e)])
  simp only [Pi.smul_apply, smul_eq_mul, e, Pi.single_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hv
  have := hd i
  nlinarith


/-- `[0, Gᵀ; G, 0] - [Diag(v), 0; 0, H Diag(w) Hᵀ]` is symmetric. -/
theorem aux_dbs_symm (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (v : Fin m → ℝ) (w : Fin l → ℝ) (a b : Fin m ⊕ Fin n) :
    (fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)) b a =
      (fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)) a b := by
  rcases a with j | k <;> rcases b with j' | k' <;>
    simp [diagonal_apply, eq_comm, mul_apply, mul_comm, mul_left_comm]
  split_ifs with h <;> simp [h]

/-- The uniformly positive definite matrices form a convex set. -/
theorem aux_dbs_convex_cone {ι : Type*} [Fintype ι] : -- --- CONCL ---
    Convex ℝ {X : Matrix ι ι ℝ |
      ∃ δ > 0, ∀ x : ι → ℝ, δ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (X *ᵥ x)} := by -- --- PROOF ---
  rintro X ⟨δ₁, hδ₁, h₁⟩ Y ⟨δ₂, hδ₂, h₂⟩ a b ha hb hab
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x => ?_⟩
  have hxx : 0 ≤ x ⬝ᵥ x := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have m1 : min δ₁ δ₂ * (x ⬝ᵥ x) ≤ δ₁ * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hxx
  have m2 : min δ₁ δ₂ * (x ⬝ᵥ x) ≤ δ₂ * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hxx
  calc min δ₁ δ₂ * (x ⬝ᵥ x) = a * (min δ₁ δ₂ * (x ⬝ᵥ x)) + b * (min δ₁ δ₂ * (x ⬝ᵥ x)) := by
        rw [← add_mul, hab, one_mul]
    _ ≤ a * (x ⬝ᵥ (X *ᵥ x)) + b * (x ⬝ᵥ (Y *ᵥ x)) :=
        add_le_add (mul_le_mul_of_nonneg_left (m1.trans (h₁ x)) ha)
          (mul_le_mul_of_nonneg_left (m2.trans (h₂ x)) hb)

/-- The relaxation's matrices at objective `≤ t` form a convex set. -/
theorem aux_dbs_convex_B (s₁ s₂ : ℝ≥0∞) [Fact (1 ≤ s₁)] [Fact (1 ≤ s₂)]
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ) (t : ℝ) : -- --- CONCL ---
    Convex ℝ {Q : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ | ∃ (v : Fin m → ℝ) (w : Fin l → ℝ),
      ‖WithLp.toLp s₁ v‖ + ‖WithLp.toLp s₂ w‖ ≤ 2 * t ∧
        Q = fromBlocks 0 Gᵀ G 0 -
          fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)} := by -- --- PROOF ---
  set M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ := fromBlocks 0 Gᵀ G 0
  set D : (Fin m → ℝ) → (Fin l → ℝ) → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
    fun v w => fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ) with hDdef
  -- a convex combination of pairs: the triangle inequality and linearity of the blocks
  rintro X ⟨v₁, w₁, hn₁, rfl⟩ Y ⟨v₂, w₂, hn₂, rfl⟩ a b ha hb hab
  refine ⟨a • v₁ + b • v₂, a • w₁ + b • w₂, ?_, ?_⟩
  · rw [WithLp.toLp_add, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul,
      WithLp.toLp_smul, WithLp.toLp_smul]
    calc ‖a • WithLp.toLp s₁ v₁ + b • WithLp.toLp s₁ v₂‖ +
          ‖a • WithLp.toLp s₂ w₁ + b • WithLp.toLp s₂ w₂‖
        ≤ (a * ‖WithLp.toLp s₁ v₁‖ + b * ‖WithLp.toLp s₁ v₂‖) +
          (a * ‖WithLp.toLp s₂ w₁‖ + b * ‖WithLp.toLp s₂ w₂‖) := by
          refine add_le_add ((norm_add_le _ _).trans ?_) ((norm_add_le _ _).trans ?_) <;>
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
              abs_of_nonneg hb]
      _ = a * (‖WithLp.toLp s₁ v₁‖ + ‖WithLp.toLp s₂ w₁‖) +
          b * (‖WithLp.toLp s₁ v₂‖ + ‖WithLp.toLp s₂ w₂‖) := by ring
      _ ≤ a * (2 * t) + b * (2 * t) :=
          add_le_add (mul_le_mul_of_nonneg_left hn₁ ha) (mul_le_mul_of_nonneg_left hn₂ hb)
      _ = 2 * t := by rw [← add_mul, hab, one_mul]
  -- the blocks are linear in `(v, w)`
  · have hDlin : D (a • v₁ + b • v₂) (a • w₁ + b • w₂) = a • D v₁ w₁ + b • D v₂ w₂ := by
      simp only [hDdef, fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]
      congr 1
      · rw [← diagonal_smul, ← diagonal_smul, diagonal_add]; rfl
      · rw [show diagonal (a • w₁ + b • w₂) = a • diagonal w₁ + b • diagonal w₂ by
          rw [← diagonal_smul, ← diagonal_smul, diagonal_add]; rfl, Matrix.mul_add,
          Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    change a • (M - D v₁ w₁) + b • (M - D v₂ w₂) = M - D (a • v₁ + b • v₂) (a • w₁ + b • w₂)
    calc a • (M - D v₁ w₁) + b • (M - D v₂ w₂)
        = (a + b) • M - (a • D v₁ w₁ + b • D v₂ w₂) := by module
      _ = M - D (a • v₁ + b • v₂) (a • w₁ + b • w₂) := by rw [hab, one_smul, hDlin]

/-- A functional below `u` on the uniformly positive definite cone is `-⟨W, ·⟩` on symmetric
matrices, `W ≽ 0`, with `u ≥ 0` and `-tr W < u`. -/
theorem aux_dbs_sep {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Matrix ι ι ℝ →L[ℝ] ℝ) (u : ℝ)
    (hfO : ∀ X ∈ {X : Matrix ι ι ℝ | ∃ δ > 0, ∀ x : ι → ℝ, δ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (X *ᵥ x)},
      f X < u) : -- --- CONCL ---
    ∃ W : Matrix ι ι ℝ, W.PosSemidef ∧ (∀ i j, W j i = W i j) ∧ 0 ≤ u ∧
      (∀ Q : Matrix ι ι ℝ, (∀ i j, Q j i = Q i j) → f Q = -∑ i, ∑ j, Q i j * W i j) ∧
      -∑ i, W i i < u := by -- --- PROOF ---
  set F : ι → ι → ℝ := fun i j => f (single i j 1) with hFdef
  have hf : ∀ X, f X = ∑ i, ∑ j, X i j * F i j := aux_dbs_functional f
  set W : Matrix ι ι ℝ := Matrix.of fun i j => -(F i j + F j i) / 2 with hWdef
  have hWsymm : ∀ i j, W j i = W i j := fun i j => by
    simp only [hWdef, of_apply]; ring
  -- on a symmetric matrix, `f Q = -⟨Q, W⟩`
  have hfsym : ∀ Q : Matrix ι ι ℝ, (∀ i j, Q j i = Q i j) →
      f Q = -∑ i, ∑ j, Q i j * W i j := fun Q hQ => by
    rw [hf]
    have h2 : ∑ i, ∑ j, Q i j * F j i = ∑ i, ∑ j, Q i j * F i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hQ]
    have : ∑ i, ∑ j, Q i j * W i j = -(1 / 2) * ∑ i, ∑ j, Q i j * F i j +
        -(1 / 2) * ∑ i, ∑ j, Q i j * F j i := by
      calc ∑ i, ∑ j, Q i j * W i j = ∑ i, ∑ j, (-(1 / 2) * (Q i j * F i j) +
            -(1 / 2) * (Q i j * F j i)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
              simp only [hWdef, of_apply]; ring
        _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [this, h2]; ring
  -- `r I + s x xᵀ` lies in the cone
  have hO1 : ∀ r : ℝ, 0 < r → ∀ s : ℝ, 0 ≤ s → ∀ x : ι → ℝ,
      f (r • (1 : Matrix ι ι ℝ) + s • vecMulVec x x) < u := by
    intro r hr s hs x
    refine hfO _ ⟨r, hr, fun y => ?_⟩
    rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : y ⬝ᵥ (vecMulVec x x *ᵥ y) = (y ⬝ᵥ x) ^ 2 := by
      rw [aux_dbs_quad]
      simp only [vecMulVec_apply, dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    nlinarith [sq_nonneg (y ⬝ᵥ x)]
  -- and `f` there is `-r tr W - s xᵀ W x`
  have hfO' : ∀ r s : ℝ, ∀ x : ι → ℝ, f (r • (1 : Matrix ι ι ℝ) + s • vecMulVec x x) =
      -(r * ∑ i, W i i) - s * (x ⬝ᵥ (W *ᵥ x)) := fun r s x => by
    rw [map_add, map_smul, map_smul, hfsym 1 (fun i j => by
        by_cases h : i = j <;> simp [one_apply, h, eq_comm]),
      hfsym (vecMulVec x x) (fun i j => by simp [vecMulVec_apply, mul_comm]), aux_dbs_quad]
    simp only [one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      vecMulVec_apply, smul_eq_mul]
    rw [mul_neg, mul_neg, ← sub_eq_add_neg]
    congr 2
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- `W ≽ 0`
  have hWq : ∀ x, 0 ≤ x ⬝ᵥ (W *ᵥ x) := fun x => by
    by_contra hneg
    push Not at hneg
    have h1 := hO1 1 one_pos (|u + ∑ i, W i i| / -(x ⬝ᵥ (W *ᵥ x)))
      (div_nonneg (abs_nonneg _) (by linarith)) x
    rw [hfO', div_mul_eq_mul_div, mul_div_assoc, show x ⬝ᵥ (W *ᵥ x) / -(x ⬝ᵥ (W *ᵥ x)) = -1 by
      rw [div_neg, div_self hneg.ne]] at h1
    linarith [le_abs_self (u + ∑ i, W i i)]
  -- so `W` is positive semidefinite
  have hWherm : W.IsHermitian := by
    ext i j; simp [hWsymm]
  have hWpsd : W.PosSemidef :=
    PosSemidef.of_dotProduct_mulVec_nonneg hWherm fun x => by simpa using hWq x
  have htr0 : 0 ≤ ∑ i, W i i := Finset.sum_nonneg fun i _ => hWpsd.diag_nonneg
  have hI := hO1 1 one_pos 0 le_rfl 0
  rw [hfO'] at hI
  refine ⟨W, hWpsd, hWsymm, ?_, hfsym, by simpa using hI⟩
  -- `u ≥ 0`: else a small multiple of `I` would reach `u`
  by_contra hneg
  push Not at hneg
  have h1 := hO1 (-u / (∑ i, W i i + 1)) (div_pos (by linarith) (by linarith)) 0 le_rfl 0
  rw [hfO'] at h1
  have : -u / (∑ i, W i i + 1) * ∑ i, W i i ≤ -u := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The pairing `⟨[0, Gᵀ; G, 0] - [Diag(v), 0; 0, H Diag(w) Hᵀ], W⟩` by blocks. -/
theorem aux_dbs_pair (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (W : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) (hWsymm : ∀ i j, W j i = W i j)
    (v : Fin m → ℝ) (w : Fin l → ℝ) : -- --- CONCL ---
    ∑ a, ∑ b, (fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)) a b *
      W a b = 2 * ∑ k, ∑ j, G k j * W (Sum.inr k) (Sum.inl j) -
        ∑ j, v j * W (Sum.inl j) (Sum.inl j) -
          ∑ i, w i * (Hᵀ * W.toBlocks₂₂ * H) i i := by -- --- PROOF ---
  have hN : ∀ i, (Hᵀ * W.toBlocks₂₂ * H) i i =
      ∑ k, ∑ k', H k i * W (Sum.inr k) (Sum.inr k') * H k' i := fun i => by
    simp only [mul_apply, transpose_apply, toBlocks₂₂, of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  -- the four blocks
  simp only [Fintype.sum_sum_type, Matrix.sub_apply, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_sub,
    sub_zero, transpose_apply, diagonal_apply, hN]
  have ha : ∑ x : Fin m, ∑ x_1, (-if x = x_1 then v x else 0) * W (Sum.inl x) (Sum.inl x_1) =
      -∑ x, v x * W (Sum.inl x) (Sum.inl x) := by
    simp [neg_mul, ite_mul, Finset.sum_ite_eq, Finset.sum_neg_distrib]
  have hb : ∑ x : Fin m, ∑ x_1, G x_1 x * W (Sum.inl x) (Sum.inr x_1) =
      ∑ k, ∑ j, G k j * W (Sum.inr k) (Sum.inl j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [hWsymm]
  have hd : ∑ x : Fin n, ∑ x_1, -(H * diagonal w * Hᵀ) x x_1 * W (Sum.inr x) (Sum.inr x_1) =
      -∑ i, w i * ∑ k, ∑ k', H k i * W (Sum.inr k) (Sum.inr k') * H k' i := by
    have hHD : ∀ x x_1, (H * diagonal w * Hᵀ) x x_1 = ∑ i, H x i * w i * H x_1 i :=
      fun x x_1 => by rw [mul_apply]; simp [mul_diagonal]
    -- reorder the triple sum
    simp only [hHD, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    calc ∑ x : Fin n, ∑ x_1 : Fin n, ∑ i : Fin l,
          H x i * w i * H x_1 i * W (Sum.inr x) (Sum.inr x_1)
        = ∑ x : Fin n, ∑ i : Fin l, ∑ x_1 : Fin n,
          H x i * w i * H x_1 i * W (Sum.inr x) (Sum.inr x_1) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ i : Fin l, ∑ x : Fin n, ∑ x_1 : Fin n,
          H x i * w i * H x_1 i * W (Sum.inr x) (Sum.inr x_1) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ha, hb, hd]
  ring

/-- With `a = -Σ G_{kj} W_{(n,k),(m,j)} > 0`, `X = (t / a) J W J` is the certificate. -/
theorem aux_dbs_certificate (s₁ s₁' s₂ s₂' : ℝ≥0∞) [Fact (1 ≤ s₁)] [Fact (1 ≤ s₂)]
    [s₁.HolderConjugate s₁'] [s₂.HolderConjugate s₂']
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (W : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) (hWpsd : W.PosSemidef)
    (hWsymm : ∀ i j, W j i = W i j) {t : ℝ} (ht : 0 < t)
    (ha : 0 < -∑ k, ∑ j, G k j * W (Sum.inr k) (Sum.inl j))
    (hv1 : ∀ v : Fin m → ℝ, ‖WithLp.toLp s₁ v‖ ≤ 2 * t →
      ∑ j, v j * W (Sum.inl j) (Sum.inl j) ≤ 2 * -∑ k, ∑ j, G k j * W (Sum.inr k) (Sum.inl j))
    (hw1 : ∀ w : Fin l → ℝ, ‖WithLp.toLp s₂ w‖ ≤ 2 * t →
      ∑ i, w i * (Hᵀ * W.toBlocks₂₂ * H) i i ≤
        2 * -∑ k, ∑ j, G k j * W (Sum.inr k) (Sum.inl j))
    (hd₂0 : ∀ i, 0 ≤ (Hᵀ * W.toBlocks₂₂ * H) i i) : -- --- CONCL ---
    ∃ X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ, X.PosSemidef ∧
      ‖WithLp.toLp s₁' (fun j => X (Sum.inl j) (Sum.inl j))‖ ≤ 1 ∧
      ‖WithLp.toLp s₂' (fun i => (Hᵀ * X.toBlocks₂₂ * H) i i)‖ ≤ 1 ∧
      t ≤ ∑ k, ∑ j, G k j * X (Sum.inr k) (Sum.inl j) := by -- --- PROOF ---
  set a : ℝ := -∑ k, ∑ j, G k j * W (Sum.inr k) (Sum.inl j) with hadef
  set σ : Fin m ⊕ Fin n → ℝ := Sum.elim (fun _ => 1) (fun _ => -1) with hσ
  set X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
    Matrix.of fun p q => t / a * σ p * σ q * W p q with hXdef
  refine ⟨X, ?_, ?_, ?_, ?_⟩
  -- `X ≽ 0`: its quadratic form is `t/a` times that of `W` at `J x`
  · refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext p q
      simp only [hXdef, conjTranspose_apply, of_apply, star_trivial, hWsymm]
      ring
    · have h := hWpsd.dotProduct_mulVec_nonneg (fun p => σ p * x p)
      simp only [star_trivial] at h ⊢
      rw [aux_dbs_quad] at h ⊢
      have e : ∑ i, ∑ j, x i * X i j * x j =
          t / a * ∑ i, ∑ j, σ i * x i * W i j * (σ j * x j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by simp only [hXdef, of_apply]; ring
      rw [e]
      exact mul_nonneg (by positivity) h
  -- the diagonals are `t/a` times those of `W`
  · have := aux_dbs_scaled_dual_le_one s₁ s₁' (fun j => W (Sum.inl j) (Sum.inl j))
      (fun j => hWpsd.diag_nonneg) ha ht hv1
    convert this using 3
    simp [hXdef, hσ]
  · have := aux_dbs_scaled_dual_le_one s₂ s₂' (fun i => (Hᵀ * W.toBlocks₂₂ * H) i i) hd₂0 ha
      ht hw1
    convert this using 3
    have hX22 : X.toBlocks₂₂ = (t / a) • W.toBlocks₂₂ := by
      ext k k'
      simp [hXdef, hσ, toBlocks₂₂]
    rw [hX22, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  -- the value is `(t/a) a = t`
  · have e : ∑ k, ∑ j, G k j * X (Sum.inr k) (Sum.inl j) = t / a * a := by
      rw [hadef, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by simp [hXdef, hσ]; ring
    rw [e, div_mul_cancel₀ _ ha.ne']

/-- A positive semidefinite `W` with `Wⱼⱼ = 0` on the first block and `diag(Hᵀ W₂₂ H) = 0`,
`H` onto, is `0`. -/
theorem aux_dbs_W_zero (H : Matrix (Fin n) (Fin l) ℝ) (hH : Function.Surjective H.mulVec)
    (W : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) (hWpsd : W.PosSemidef)
    (hd₁ : ∀ j, W (Sum.inl j) (Sum.inl j) = 0)
    (hd₂ : ∀ i, (Hᵀ * W.toBlocks₂₂ * H) i i = 0) : -- --- CONCL ---
    ∀ p q, W p q = 0 := by -- --- PROOF ---
  set N : Matrix (Fin l) (Fin l) ℝ := Hᵀ * W.toBlocks₂₂ * H with hNdef
  have hNpsd : N.PosSemidef := by
    have h22 : W.toBlocks₂₂ = W.submatrix Sum.inr Sum.inr := rfl
    have := (hWpsd.submatrix Sum.inr).conjTranspose_mul_mul_same H
    rw [conjTranspose_eq_transpose_of_trivial] at this
    rw [hNdef, h22]
    exact this
  -- `Hᵀ W₂₂ H ≽ 0` with zero diagonal vanishes
  have hN0 : ∀ i i', N i i' = 0 := fun i i' => by
    have h := aux_dbs_abs_le hNpsd i i'
    rw [hd₂ i, hd₂ i'] at h
    exact abs_nonpos_iff.mp (by linarith)
  -- so `W₂₂` vanishes at each `eₖ = H β`
  have hWd : ∀ p, W p p = 0 := by
    rintro (j | k)
    · exact hd₁ j
    · obtain ⟨β, hβ⟩ := hH (Pi.single k 1)
      have hq : β ⬝ᵥ (N *ᵥ β) = (H *ᵥ β) ⬝ᵥ (W.toBlocks₂₂ *ᵥ (H *ᵥ β)) := by
        rw [hNdef, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      have h0 : β ⬝ᵥ (N *ᵥ β) = 0 := by
        rw [aux_dbs_quad]
        simp [hN0]
      rw [h0, hβ, aux_dbs_quad] at hq
      simpa [Pi.single_apply, toBlocks₂₂] using hq.symm
  -- a zero diagonal makes all of `W ≽ 0` vanish
  intro p q
  have h := aux_dbs_abs_le hWpsd p q
  rw [hWd, hWd] at h
  exact abs_nonpos_iff.mp (by linarith)


-- =======================================  MAIN THEOREM  ======================================= --

theorem diag_block_sdp_exists_dual (s₁ s₁' s₂ s₂' : ℝ≥0∞) [Fact (1 ≤ s₁)] [Fact (1 ≤ s₂)]
    [s₁.HolderConjugate s₁'] [s₂.HolderConjugate s₂']
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) {t : ℝ} (ht : 0 < t)
    (hK : ∀ (v : Fin m → ℝ) (w : Fin l → ℝ),
      (fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)).PosSemidef →
      t < (‖WithLp.toLp s₁ v‖ + ‖WithLp.toLp s₂ w‖) / 2) : -- --- CONCL ---
    ∃ X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ, X.PosSemidef ∧
      ‖WithLp.toLp s₁' (fun j => X (Sum.inl j) (Sum.inl j))‖ ≤ 1 ∧
      ‖WithLp.toLp s₂' (fun i => (Hᵀ * X.toBlocks₂₂ * H) i i)‖ ≤ 1 ∧
      t ≤ ∑ k, ∑ j, G k j * X (Sum.inr k) (Sum.inl j) := by -- --- PROOF ---
  classical
  -- the cone misses the relaxation's matrices at objective `≤ t`, none of them `≽ 0`
  have hdisj : Disjoint
      {X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ |
        ∃ δ > 0, ∀ x : Fin m ⊕ Fin n → ℝ, δ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (X *ᵥ x)}
      {Q | ∃ (v : Fin m → ℝ) (w : Fin l → ℝ), ‖WithLp.toLp s₁ v‖ + ‖WithLp.toLp s₂ w‖ ≤ 2 * t ∧
        Q = fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)} := by
    rw [Set.disjoint_left]
    rintro X ⟨δ, hδ, hX⟩ ⟨v, w, hvw, rfl⟩
    -- a uniformly positive definite member would be `≽ 0`, so in `K`
    have hherm : (fromBlocks 0 Gᵀ G 0 -
        fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)).IsHermitian := by
      ext a b
      rw [conjTranspose_apply, star_trivial]
      exact aux_dbs_symm G H v w a b
    have hpsd := PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => by
      have hxx : 0 ≤ x ⬝ᵥ x := by
        simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      simp only [star_trivial]
      nlinarith [hX x]
    have := hK v w hpsd
    linarith
  obtain ⟨f, u, hfO, hfB⟩ := geometric_hahn_banach_open aux_dbs_convex_cone aux_dbs_isOpen
    (aux_dbs_convex_B s₁ s₂ G H t) hdisj
  obtain ⟨W, hWpsd, hWsymm, hu, hfsym, hI⟩ := aux_dbs_sep f u hfO
  -- the separation on the relaxation's side: `2V ≤ Σ vⱼ Wⱼⱼ + Σ wᵢ (Hᵀ W₂₂ H)ᵢᵢ`
  set V : ℝ := ∑ k, ∑ j, G k j * W (Sum.inr k) (Sum.inl j) with hVdef
  have hB : ∀ (v : Fin m → ℝ) (w : Fin l → ℝ), ‖WithLp.toLp s₁ v‖ + ‖WithLp.toLp s₂ w‖ ≤ 2 * t →
      2 * V ≤ ∑ j, v j * W (Sum.inl j) (Sum.inl j) + ∑ i, w i * (Hᵀ * W.toBlocks₂₂ * H) i i :=
    fun v w hvw => by
      have h := hfB _ ⟨v, w, hvw, rfl⟩
      rw [hfsym _ (aux_dbs_symm G H v w), aux_dbs_pair G H W hWsymm] at h
      linarith
  -- `-v` and `-w` alone bound each diagonal
  have hv1 : ∀ v : Fin m → ℝ, ‖WithLp.toLp s₁ v‖ ≤ 2 * t →
      ∑ j, v j * W (Sum.inl j) (Sum.inl j) ≤ 2 * -V := fun v hv => by
    have h := hB (-v) 0 (by
      rw [WithLp.toLp_neg, norm_neg, WithLp.toLp_zero, norm_zero, add_zero]; exact hv)
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero] at h
    linarith
  have hw1 : ∀ w : Fin l → ℝ, ‖WithLp.toLp s₂ w‖ ≤ 2 * t →
      ∑ i, w i * (Hᵀ * W.toBlocks₂₂ * H) i i ≤ 2 * -V := fun w hw => by
    have h := hB 0 (-w) (by
      rw [WithLp.toLp_neg, norm_neg, WithLp.toLp_zero, norm_zero, zero_add]; exact hw)
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add] at h
    linarith
  have hd₂0 : ∀ i, 0 ≤ (Hᵀ * W.toBlocks₂₂ * H) i i := fun i => by
    have h22 : W.toBlocks₂₂ = W.submatrix Sum.inr Sum.inr := rfl
    have := (hWpsd.submatrix Sum.inr).conjTranspose_mul_mul_same H
    rw [conjTranspose_eq_transpose_of_trivial, ← h22] at this
    exact this.diag_nonneg
  -- the two cases of the sign of `-V`
  rcases lt_or_ge 0 (-V) with ha | ha
  · exact aux_dbs_certificate s₁ s₁' s₂ s₂' G H W hWpsd hWsymm ht ha hv1 hw1 hd₂0
  · -- both diagonals vanish, so `W = 0`, and `f` cannot separate
    have hd₁ := aux_dbs_eq_zero s₁ _ (fun j => hWpsd.diag_nonneg) ht fun v hv =>
      (hv1 v hv).trans (by linarith)
    have hd₂ := aux_dbs_eq_zero s₂ _ hd₂0 ht fun w hw => (hw1 w hw).trans (by linarith)
    have hW0 := aux_dbs_W_zero H hH W hWpsd hd₁ hd₂
    simp only [hW0, Finset.sum_const_zero, neg_zero] at hI
    have h3 := hfB _ ⟨0, 0, by simp; linarith, rfl⟩
    rw [hfsym _ (aux_dbs_symm G H 0 0)] at h3
    simp only [hW0, mul_zero, Finset.sum_const_zero, neg_zero] at h3
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
