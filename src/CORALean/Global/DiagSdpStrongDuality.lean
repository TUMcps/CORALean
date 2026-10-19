module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# Strong duality for the semidefinite relaxation with unit diagonal

[1, Eq. 19]: for a symmetric `A ∈ ℝ^{m×m}`, `max ⟨A, U⟩` s.t. `U ≽ 0`, `Uᵢᵢ = 1`, and its dual
`min 1ᵀλ` s.t. `diag(λ) - A ≽ 0` both attain their optima, and the optima agree. The paper cites
convexity and constraint qualifications; here the dual is built by separation.

Weak duality is `⟨diag(λ) - A, U⟩ ≥ 0`. Let `p` be the primal maximum, attained on the compact
correlation matrices (`|Uᵢⱼ| ≤ 1`), and `ε > 0`. If no `diag(λ) - A`, `1ᵀλ = p + ε`, were
uniformly positive definite, that open convex cone would miss the affine set of them, and some
`X ↦ -⟨W, X⟩` would separate the two (`geometric_hahn_banach_open`). Bounded above on the cone,
`W ≽ 0`; bounded below on the affine set, `W` has one constant diagonal `w`, positive as a
semidefinite matrix with zero diagonal is zero. Then `W / w` is primal feasible, `⟨A, W⟩ ≤ w p`,
and the functional is at most `-wε < 0` on the affine set, below the level `≥ 0`: Slater's
condition through the open cone. The dual optimum is attained on the compact
`{λ | diag(λ) - A ≽ 0, 1ᵀλ ≤ p + 1}`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `xᵀ M x` as a double sum. -/
theorem aux_sdpDual_quad (M : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form at `eᵢ + s eⱼ`. -/
theorem aux_sdpDual_quad_pair (M : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) (s : ℝ) :
    (Pi.single i 1 + Pi.single j s : Fin m → ℝ) ⬝ᵥ (M *ᵥ (Pi.single i 1 + Pi.single j s)) =
      M i i + s * M i j + s * M j i + s * s * M j j := by
  rw [aux_sdpDual_quad]
  simp only [Pi.add_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq']
  ring

/-- A positive semidefinite real matrix has `|Mᵢⱼ| ≤ (Mᵢᵢ + Mⱼⱼ) / 2`. -/
theorem aux_sdpDual_abs_le {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosSemidef) (i j : Fin m) :
    |M i j| ≤ (M i i + M j j) / 2 := by -- --- PROOF ---
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg hM.diag_nonneg]; linarith
  have hsym : M j i = M i j := by
    have := hM.isHermitian.apply i j
    simpa using this
  have h1 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j (-1))
  simp only [star_trivial] at h1 h2
  rw [aux_sdpDual_quad_pair M i j] at h1 h2
  rw [abs_le]; constructor <;> nlinarith

/-- The positive semidefinite matrices form a closed set. -/
theorem aux_sdpDual_isClosed_posSemidef :
    IsClosed {M : Matrix (Fin m) (Fin m) ℝ | M.PosSemidef} := by -- --- PROOF ---
  have : {M : Matrix (Fin m) (Fin m) ℝ | M.PosSemidef} =
      {M | Mᴴ = M} ∩ ⋂ x : Fin m → ℝ, {M | 0 ≤ x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp [posSemidef_iff_dotProduct_mulVec, IsHermitian]
  rw [this]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun x => ?_)
  exact isClosed_le continuous_const (by fun_prop)

/-- `⟨M, U⟩ ≥ 0` for positive semidefinite `M` and `U`. -/
theorem aux_sdpDual_trace_mul_nonneg {M U : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosSemidef)
    (hU : U.PosSemidef) : 0 ≤ (M * U).trace := by -- --- PROOF ---
  obtain ⟨k, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hU
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_nonneg fun l _ => ?_
  have h := hM.dotProduct_mulVec_nonneg (v l)
  simp only [star_trivial] at h ⊢
  rw [aux_sdpDual_quad] at h
  convert h using 1
  simp only [trace, diag, mul_apply, vecMulVec_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Weak duality: `⟨A, U⟩ ≤ 1ᵀλ`. -/
theorem aux_sdpDual_weak {A U : Matrix (Fin m) (Fin m) ℝ} {lam : Fin m → ℝ}
    (hU : U.PosSemidef) (hdiag : ∀ i, U i i = 1) (hlam : (diagonal lam - A).PosSemidef) :
    (A * U).trace ≤ ∑ i, lam i := by -- --- PROOF ---
  have h := aux_sdpDual_trace_mul_nonneg hlam hU
  rw [Matrix.sub_mul, Matrix.trace_sub] at h
  have hd : (diagonal lam * U).trace = ∑ i, lam i := by
    simp [trace, diagonal_mul, hdiag]
  linarith

/-- A linear functional on matrices is `X ↦ ∑ Xᵢⱼ f(Eᵢⱼ)`. -/
theorem aux_sdpDual_functional (f : Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)
    (X : Matrix (Fin m) (Fin m) ℝ) :
    f X = ∑ i, ∑ j, X i j * f (single i j 1) := by -- --- PROOF ---
  conv_lhs => rw [matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single i j (X i j) = X i j • single i j (1 : ℝ) by
    rw [smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

/-- The uniformly positive definite matrices form an open set. -/
theorem aux_sdpDual_isOpen (hm : 0 < m) :
    IsOpen {X : Matrix (Fin m) (Fin m) ℝ |
      ∃ δ > 0, ∀ x : Fin m → ℝ, δ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (X *ᵥ x)} := by -- --- PROOF ---
  rw [isOpen_iff_forall_mem_open]
  rintro X ⟨δ, hδ, hX⟩
  set r : ℝ := δ / (2 * m) with hr
  have hrpos : 0 < r := div_pos hδ (by positivity)
  refine ⟨{Y | ∀ i j, |Y i j - X i j| < r}, fun Y hY => ⟨δ / 2, half_pos hδ, fun x => ?_⟩,
    ?_, fun i j => by simpa using hrpos⟩
  · -- `|xᵀ(Y - X)x| ≤ r ∑∑ (xᵢ² + xⱼ²)/2 = r m xᵀx = δ/2 xᵀx`
    have hdiff : x ⬝ᵥ (X *ᵥ x) - x ⬝ᵥ (Y *ᵥ x) ≤ (δ / 2) * (x ⬝ᵥ x) := by
      rw [aux_sdpDual_quad, aux_sdpDual_quad, ← Finset.sum_sub_distrib]
      -- entrywise, `|Yᵢⱼ - Xᵢⱼ| < r` and `|xᵢxⱼ| ≤ (xᵢ² + xⱼ²)/2`
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
      -- summed, `∑∑ (xᵢ² + xⱼ²)/2 = m xᵀx`
      calc ∑ i, (∑ j, x i * X i j * x j - ∑ j, x i * Y i j * x j)
          = ∑ i, ∑ j, (x i * X i j * x j - x i * Y i j * x j) := by
            simp only [Finset.sum_sub_distrib]
        _ ≤ ∑ i : Fin m, ∑ j : Fin m, r * ((x i * x i + x j * x j) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
        _ = (δ / 2) * (x ⬝ᵥ x) := by
            have hm' : (m : ℝ) ≠ 0 := by positivity
            simp only [dotProduct, add_div, mul_add, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
              ← Finset.sum_div]
            rw [hr]
            field_simp
            ring
    linarith [hX x]
  · -- the neighbourhood is a finite intersection of open slabs
    have : {Y : Matrix (Fin m) (Fin m) ℝ | ∀ i j, |Y i j - X i j| < r} =
        ⋂ i, ⋂ j, {Y | |Y i j - X i j| < r} := by
      ext Y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (by fun_prop) continuous_const

/-- The separating functional cannot exist: it would make `W / w` beat the primal maximum. -/
theorem aux_sdpDual_contra (A : Matrix (Fin m) (Fin m) ℝ) (hA : Aᵀ = A) (hm : 0 < m) (p : ℝ)
    (hp : ∀ U : Matrix (Fin m) (Fin m) ℝ, U.PosSemidef → (∀ i, U i i = 1) → (A * U).trace ≤ p)
    {ε : ℝ} (hε : 0 < ε) (f : Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) (u : ℝ)
    (hfO : ∀ X ∈ {X : Matrix (Fin m) (Fin m) ℝ |
      ∃ δ > 0, ∀ x : Fin m → ℝ, δ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (X *ᵥ x)}, f X < u)
    (hfK : ∀ lam : Fin m → ℝ, ∑ i, lam i = p + ε → u ≤ f (diagonal lam - A)) : -- --- CONCL ---
    False := by -- --- PROOF ---
  have hAij : ∀ i j, A j i = A i j := fun i j => by
    simpa using congrFun (congrFun hA i) j
  set F : Fin m → Fin m → ℝ := fun i j => f (single i j 1) with hFdef
  have hf : ∀ X, f X = ∑ i, ∑ j, X i j * F i j := aux_sdpDual_functional f
  -- `f` on the cone: `t I + s x xᵀ` lies in it
  have hf1 : f 1 = ∑ i, F i i := by
    rw [hf]; simp [one_apply]
  have hfxx : ∀ x : Fin m → ℝ, f (vecMulVec x x) = ∑ i, ∑ j, x i * x j * F i j := fun x => by
    rw [hf]; simp [vecMulVec_apply]
  -- `t I + s x xᵀ` is uniformly positive definite, `t > 0`, `s ≥ 0`
  have hO1 : ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 ≤ s → ∀ x : Fin m → ℝ,
      f (t • (1 : Matrix (Fin m) (Fin m) ℝ) + s • vecMulVec x x) < u := by
    intro t ht s hs x
    refine hfO _ ⟨t, ht, fun y => ?_⟩
    rw [aux_sdpDual_quad]
    have hsq : 0 ≤ s * (∑ i, y i * x i) ^ 2 := by positivity
    -- `yᵀ(t I + s x xᵀ)y = t yᵀy + s (yᵀx)²`
    have : ∑ i, ∑ j, y i * (t • (1 : Matrix (Fin m) (Fin m) ℝ) + s • vecMulVec x x) i j * y j =
        t * ∑ i, y i * y i + s * (∑ i, y i * x i) ^ 2 := by
      simp only [Matrix.add_apply, Matrix.smul_apply, one_apply, vecMulVec_apply, smul_eq_mul,
        mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, sq, Finset.sum_mul, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [dotProduct]
    linarith
  have hfO' : ∀ t s : ℝ, ∀ x : Fin m → ℝ,
      f (t • (1 : Matrix (Fin m) (Fin m) ℝ) + s • vecMulVec x x) =
        t * ∑ i, F i i + s * ∑ i, ∑ j, x i * x j * F i j := fun t s x => by
    rw [map_add, map_smul, map_smul, hf1, hfxx, smul_eq_mul, smul_eq_mul]
  -- `f(x xᵀ) ≤ 0`
  have hq : ∀ x : Fin m → ℝ, ∑ i, ∑ j, x i * x j * F i j ≤ 0 := fun x => by
    by_contra hpos
    push Not at hpos
    have h0 := hO1 1 one_pos 0 le_rfl x
    rw [hfO'] at h0
    have h1 := hO1 1 one_pos ((u - ∑ i, F i i) / ∑ i, ∑ j, x i * x j * F i j)
      (div_nonneg (by linarith) hpos.le) x
    rw [hfO', div_mul_cancel₀ _ hpos.ne'] at h1
    linarith
  -- the level is non-negative
  have hu : 0 ≤ u := by
    by_contra hneg
    push Not at hneg
    rcases le_or_gt 0 (∑ i, F i i) with h | h
    · have := hO1 1 one_pos 0 le_rfl 0
      rw [hfO'] at this; linarith
    · have ht : 0 < u / (2 * ∑ i, F i i) := div_pos_of_neg_of_neg hneg (by linarith)
      have := hO1 _ ht 0 le_rfl 0
      rw [hfO'] at this
      have hS : ∑ i, F i i ≠ 0 := h.ne
      have e : u / (2 * ∑ i, F i i) * ∑ i, F i i = u / 2 := by field_simp
      linarith
  -- `f` on the affine set
  have hfK' : ∀ lam : Fin m → ℝ, f (diagonal lam - A) =
      ∑ i, lam i * F i i - ∑ i, ∑ j, A i j * F i j := fun lam => by
    rw [hf]
    simp only [Matrix.sub_apply, diagonal_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set i₀ : Fin m := ⟨0, hm⟩
  set c₀ : ℝ := (p + ε) / m with hc₀
  have hmR : (m : ℝ) ≠ 0 := by positivity
  -- a bounded-below line of the affine set: the diagonal of `F` is constant
  have hFdiag : ∀ i, F i i = F i₀ i₀ := fun i => by
    by_contra hD
    have hD' : F i i - F i₀ i₀ ≠ 0 := sub_ne_zero.mpr hD
    set C : ℝ := c₀ * ∑ k, F k k - ∑ k, ∑ j, A k j * F k j
    have hline : ∀ s : ℝ, u ≤ C + s * (F i i - F i₀ i₀) := fun s => by
      set lam : Fin m → ℝ := fun k =>
        c₀ + s * ((if k = i then 1 else 0) - (if k = i₀ then 1 else 0)) with hlam
      -- `λ = c₀ + s(eᵢ - eᵢ₀)` stays on the affine set
      have hsum : ∑ k, lam k = p + ε := by
        simp only [hlam, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self, mul_zero, add_zero, hc₀]
        field_simp
      have h := hfK lam hsum
      rw [hfK'] at h
      have e : ∑ k, lam k * F k k = c₀ * ∑ k, F k k + s * (F i i - F i₀ i₀) := by
        simp only [hlam, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc,
          sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      rw [e] at h
      linarith
    -- a non-zero slope would push `f` below `u`
    have := hline ((u - C - 1) / (F i i - F i₀ i₀))
    rw [div_mul_cancel₀ _ hD'] at this
    linarith
  -- `W = -(F + Fᵀ)/2` is positive semidefinite with constant diagonal `w`
  set W : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => -(F i j + F j i) / 2 with hWdef
  set w : ℝ := -F i₀ i₀ with hw
  have hWsymm : ∀ i j, W j i = W i j := fun i j => by
    simp only [hWdef, of_apply]; ring
  have hWherm : W.IsHermitian := by
    ext i j; simp [hWsymm]
  -- `xᵀWx = -xᵀFx ≥ 0`
  have hWq : ∀ x : Fin m → ℝ, 0 ≤ x ⬝ᵥ (W *ᵥ x) := fun x => by
    rw [aux_sdpDual_quad]
    have e : ∑ i, ∑ j, x i * W i j * x j = -(1 / 2) * ∑ i, ∑ j, x i * x j * F i j +
        -(1 / 2) * ∑ i, ∑ j, x i * x j * F j i := by
      calc ∑ i, ∑ j, x i * W i j * x j = ∑ i, ∑ j, (-(1 / 2) * (x i * x j * F i j) +
            -(1 / 2) * (x i * x j * F j i)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
              simp only [hWdef, of_apply]; ring
        _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h2 : ∑ i, ∑ j, x i * x j * F j i = ∑ i, ∑ j, x i * x j * F i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e, h2]
    linarith [hq x]
  -- so `W ≽ 0`, with diagonal `w ≥ 0`
  have hWpsd : W.PosSemidef :=
    PosSemidef.of_dotProduct_mulVec_nonneg hWherm fun x => by simpa using hWq x
  have hWdiag : ∀ i, W i i = w := fun i => by
    simp only [hWdef, of_apply, hw, hFdiag i]; ring
  have hw0 : 0 ≤ w := hWdiag i₀ ▸ hWpsd.diag_nonneg
  -- `f` at the cone's `I` and at the affine set's `diag((p + ε)/m) - A`
  have hsumF : ∑ i, F i i = -(m * w) := by
    simp only [hFdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hw]
    ring
  have hlt : -(m * w) < u := by
    have := hO1 1 one_pos 0 le_rfl 0
    rw [hfO', hsumF] at this; linarith
  -- `⟨A, F⟩ = -⟨A, W⟩`, `A` being symmetric
  have hAW : ∑ i, ∑ j, A i j * F i j = -∑ i, ∑ j, A i j * W i j := by
    have h2 : ∑ i, ∑ j, A i j * F j i = ∑ i, ∑ j, A i j * F i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hAij]
    have : ∑ i, ∑ j, A i j * W i j = -(1 / 2) * ∑ i, ∑ j, A i j * F i j +
        -(1 / 2) * ∑ i, ∑ j, A i j * F j i := by
      calc ∑ i, ∑ j, A i j * W i j = ∑ i, ∑ j, (-(1 / 2) * (A i j * F i j) +
            -(1 / 2) * (A i j * F j i)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
              simp only [hWdef, of_apply]; ring
        _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [this, h2]; ring
  have hY : u ≤ -((p + ε) * w) + ∑ i, ∑ j, A i j * W i j := by
    have h := hfK (fun _ => c₀) (by simp [Finset.sum_const, hc₀]; field_simp)
    rw [hfK', ← Finset.mul_sum, hsumF, hAW, hc₀] at h
    have e : (p + ε) / m * -(m * w) = -((p + ε) * w) := by field_simp
    linarith
  rcases hw0.lt_or_eq with hwpos | hw0'
  · -- `W / w` is primal feasible
    have hU : ((1 / w) • W).PosSemidef := hWpsd.smul (by positivity)
    have hUd : ∀ i, ((1 / w) • W) i i = 1 := fun i => by
      rw [Matrix.smul_apply, hWdiag, smul_eq_mul, one_div, inv_mul_cancel₀ hwpos.ne']
    have hpU := hp _ hU hUd
    -- `⟨A, W/w⟩ ≤ p`, so `f ≤ -εw < 0 ≤ u` on the affine set
    have htr : (A * ((1 / w) • W)).trace = (1 / w) * ∑ i, ∑ j, A i j * W i j := by
      rw [Matrix.mul_smul, trace_smul, smul_eq_mul]
      congr 1
      simp only [trace, diag, mul_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hWsymm]
    rw [htr] at hpU
    have hAWle : ∑ i, ∑ j, A i j * W i j ≤ w * p := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hwpos] at hpU; linarith
    have e : -((p + ε) * w) = -(w * p) - ε * w := by ring
    have hεw : 0 < ε * w := mul_pos hε hwpos
    linarith
  · -- `W = 0`, so `f` vanishes on symmetric matrices
    have hW0 : ∀ i j, W i j = 0 := fun i j => by
      have h := aux_sdpDual_abs_le hWpsd i j
      rw [hWdiag, hWdiag, ← hw0'] at h
      exact abs_nonpos_iff.mp (by linarith)
    simp only [hW0, mul_zero, Finset.sum_const_zero, ← hw0'] at hY hlt
    linarith


/-- The separation step: for `ε > 0` some `λ` with `1ᵀλ = p + ε` is dual feasible. -/
theorem aux_sdpDual_exists (A : Matrix (Fin m) (Fin m) ℝ) (hA : Aᵀ = A) (hm : 0 < m) (p : ℝ)
    (hp : ∀ U : Matrix (Fin m) (Fin m) ℝ, U.PosSemidef → (∀ i, U i i = 1) → (A * U).trace ≤ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : Fin m → ℝ, (diagonal lam - A).PosSemidef ∧ ∑ i, lam i = p + ε := by -- --- PROOF ---
  have hAij : ∀ i j, A j i = A i j := fun i j => by
    simpa using congrFun (congrFun hA i) j
  have hherm : ∀ lam : Fin m → ℝ, (diagonal lam - A).IsHermitian := fun lam => by
    rw [IsHermitian, conjTranspose_sub, diagonal_conjTranspose, star_trivial,
      conjTranspose_eq_transpose_of_trivial, hA]
  by_contra hne
  push Not at hne
  -- the open cone of uniformly positive definite matrices, and the affine set of `diag(λ) - A`
  set O : Set (Matrix (Fin m) (Fin m) ℝ) :=
    {X | ∃ δ > 0, ∀ x : Fin m → ℝ, δ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (X *ᵥ x)} with hOdef
  set K : Set (Matrix (Fin m) (Fin m) ℝ) :=
    {X | ∃ lam : Fin m → ℝ, ∑ i, lam i = p + ε ∧ X = diagonal lam - A} with hKdef
  -- the cone is convex: the smaller `δ` works for a convex combination
  have hOc : Convex ℝ O := by
    rintro X ⟨δ₁, hδ₁, h₁⟩ Y ⟨δ₂, hδ₂, h₂⟩ a b ha hb hab
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x => ?_⟩
    have hxx : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have e1 := h₁ x
    have e2 := h₂ x
    have m1 : min δ₁ δ₂ * (x ⬝ᵥ x) ≤ δ₁ * (x ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hxx
    have m2 : min δ₁ δ₂ * (x ⬝ᵥ x) ≤ δ₂ * (x ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hxx
    calc min δ₁ δ₂ * (x ⬝ᵥ x) = a * (min δ₁ δ₂ * (x ⬝ᵥ x)) + b * (min δ₁ δ₂ * (x ⬝ᵥ x)) := by
          rw [← add_mul, hab, one_mul]
      _ ≤ a * (x ⬝ᵥ (X *ᵥ x)) + b * (x ⬝ᵥ (Y *ᵥ x)) :=
          add_le_add (mul_le_mul_of_nonneg_left (m1.trans e1) ha)
            (mul_le_mul_of_nonneg_left (m2.trans e2) hb)
  have hOo : IsOpen O := aux_sdpDual_isOpen hm
  -- the affine set is convex, and the cone misses it
  have hKc : Convex ℝ K := by
    rintro X ⟨l₁, hl₁, rfl⟩ Y ⟨l₂, hl₂, rfl⟩ a b ha hb hab
    refine ⟨a • l₁ + b • l₂, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hl₁, hl₂]
      rw [← add_mul, hab, one_mul]
    · ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, diagonal_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> linear_combination (-(A i j)) * hab
  have hdisj : Disjoint O K := by
    rw [Set.disjoint_left]
    rintro X ⟨δ, hδ, hX⟩ ⟨lam, hlam, rfl⟩
    refine hne lam (PosSemidef.of_dotProduct_mulVec_nonneg (hherm lam) fun x => ?_) hlam
    have hxx : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    simp only [star_trivial]
    nlinarith [hX x]
  -- a functional separates them, which `aux_sdpDual_contra` rules out
  obtain ⟨f, u, hfO, hfK⟩ := geometric_hahn_banach_open hOc hOo hKc hdisj
  exact aux_sdpDual_contra A hA hm p hp hε f u hfO fun lam hlam => hfK _ ⟨lam, hlam, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Strong duality: `max {⟨A, U⟩ | U ≽ 0, Uᵢᵢ = 1} = min {1ᵀλ | diag(λ) - A ≽ 0}`, both attained. -/
theorem diag_sdp_strong_duality (A : Matrix (Fin m) (Fin m) ℝ) (hA : Aᵀ = A) : -- --- CONCL ---
    ∃ d : ℝ,
      IsGreatest {t | ∃ U : Matrix (Fin m) (Fin m) ℝ,
        U.PosSemidef ∧ (∀ i, U i i = 1) ∧ t = (A * U).trace} d ∧
      IsLeast {t | ∃ lam : Fin m → ℝ,
        (diagonal lam - A).PosSemidef ∧ t = ∑ i, lam i} d := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- no coordinates: both programs are `0`
    have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℝ, M = 0 := fun M => Subsingleton.elim _ _
    refine ⟨0, ⟨⟨1, PosSemidef.one, fun i => i.elim0, by simp⟩, ?_⟩,
      ⟨⟨0, by rw [h0 (diagonal 0 - A)]; exact PosSemidef.zero, by simp⟩, ?_⟩⟩
    · rintro _ ⟨U, -, -, rfl⟩; simp
    · rintro _ ⟨lam, -, rfl⟩; simp
  -- the primal maximum, on the compact set of correlation matrices
  set S : Set (Matrix (Fin m) (Fin m) ℝ) := {U | U.PosSemidef ∧ ∀ i, U i i = 1} with hSdef
  have hSc : IsCompact S := by
    have hbox : IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin m =>
        Set.Icc (-1 : ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    refine hbox.of_isClosed_subset ?_ ?_
    · -- closed, and inside the box `|Uᵢⱼ| ≤ 1`
      have : S = {U | U.PosSemidef} ∩ ⋂ i, {U : Matrix (Fin m) (Fin m) ℝ | U i i = 1} := by
        ext U; simp [hSdef]
      rw [this]
      exact aux_sdpDual_isClosed_posSemidef.inter
        (isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const)
    · rintro U ⟨hU, hd⟩ i - j -
      have := aux_sdpDual_abs_le hU i j
      rw [hd, hd] at this
      exact abs_le.mp (by linarith)
  obtain ⟨U₀, hU₀, hmax⟩ := hSc.exists_isMaxOn ⟨1, PosSemidef.one, fun i => by simp⟩
    (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun U => (A * U).trace) S)
  set p := (A * U₀).trace with hpdef
  have hp : ∀ U : Matrix (Fin m) (Fin m) ℝ, U.PosSemidef → (∀ i, U i i = 1) →
      (A * U).trace ≤ p := fun U hU hd => hmax ⟨hU, hd⟩
  -- the dual minimum, on the compact set `diag(λ) - A ≽ 0`, `1ᵀλ ≤ p + 1`
  set T : Set (Fin m → ℝ) := {lam | (diagonal lam - A).PosSemidef ∧ ∑ i, lam i ≤ p + 1}
    with hTdef
  have hTc : IsCompact T := by
    have hbox : IsCompact (Set.univ.pi fun i : Fin m =>
        Set.Icc (A i i) (A i i + (p + 1 - ∑ j, A j j))) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    refine hbox.of_isClosed_subset ?_ ?_
    · -- closed, and inside the box `Aᵢᵢ ≤ λᵢ ≤ Aᵢᵢ + p + 1 - tr A`
      exact (aux_sdpDual_isClosed_posSemidef.preimage
        (by fun_prop : Continuous fun lam : Fin m → ℝ => diagonal lam - A)).inter
        (isClosed_le (by fun_prop : Continuous fun lam : Fin m → ℝ => ∑ i, lam i)
          continuous_const)
    · rintro lam ⟨hlam, hsum⟩ i -
      have hdiag : ∀ j, A j j ≤ lam j := fun j => by
        have := hlam.diag_nonneg (i := j)
        simp only [Matrix.sub_apply, diagonal_apply_eq] at this
        linarith
      have hle : lam i - A i i ≤ ∑ j, (lam j - A j j) :=
        Finset.single_le_sum (f := fun j => lam j - A j j)
          (fun j _ => sub_nonneg.mpr (hdiag j)) (Finset.mem_univ i)
      rw [Finset.sum_sub_distrib] at hle
      exact ⟨hdiag i, by linarith⟩
  -- the dual set is non-empty by the separation step at `ε = 1`
  obtain ⟨lam₁, hlam₁, hsum₁⟩ := aux_sdpDual_exists A hA hm p hp one_pos
  obtain ⟨lam₀, ⟨hlam₀, -⟩, hmin⟩ := hTc.exists_isMinOn ⟨lam₁, hlam₁, hsum₁.le⟩
    (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun lam => ∑ i, lam i) T)
  -- `1ᵀλ₀ = p`: at least `p` by weak duality, at most `p + ε` for every `ε > 0`
  have hval : ∑ i, lam₀ i = p := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
      (aux_sdpDual_weak hU₀.1 hU₀.2 hlam₀)
    rcases le_or_gt ε 1 with hε1 | hε1
    · obtain ⟨lam, hlam, hsum⟩ := aux_sdpDual_exists A hA hm p hp hε
      have := hmin ⟨hlam, by linarith⟩
      simp only [Set.mem_setOf_eq] at this
      linarith
    · have := hmin ⟨hlam₁, hsum₁.le⟩
      simp only [Set.mem_setOf_eq] at this
      linarith
  -- both optima are `p`
  refine ⟨p, ⟨⟨U₀, hU₀.1, hU₀.2, rfl⟩, ?_⟩, ⟨⟨lam₀, hlam₀, hval.symm⟩, ?_⟩⟩
  · rintro _ ⟨U, hU, hd, rfl⟩; exact hp U hU hd
  · rintro _ ⟨lam, hlam, rfl⟩; exact aux_sdpDual_weak hU₀.1 hU₀.2 hlam

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
