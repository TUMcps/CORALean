import CORALean.Global.CoeffNorm
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The linear relaxation is exact when the dual maximizer has equal columns

[1, Thm. 16]: for `G ∈ ℝ^{n×m}`, `H ∈ ℝ^{n×l}` and `Y` a maximizer of the dual program (Eq. 33),
`max tr(Gᵀ Y)` subject to `‖Hᵀ Y‖_{L⊤∞,q*} ≤ 1`, whose columns are equal up to sign (Eq. 34),
`LR_q(G, H) = r(Z(G), E_q(H))`: the minimum of Eq. 29 and the maximum of Eq. 15 exist and agree.
`H` need not be surjective: a maximizer forces `G`'s columns into the range of `H`, since
otherwise a `Z` with `Hᵀ Z = 0` and `tr(Gᵀ Z) ≠ 0` makes the program unbounded.
Strong duality of Eq. 32 is proved for this instance: on `ℝ^{l×m}` normed by `‖·‖_{L⊤₁,q}` (a
`PiLp q` of `PiLp 1`), `LR_q` is the distance from a feasible point to the kernel `K` of
`X ↦ H X`, a functional of norm `≤ 1` on the quotient by `K` attains it (Hahn–Banach), it
factors through `X ↦ H X` as `X ↦ tr(Yᵀ H X)`, and its norm bound gives
`‖Hᵀ Y‖_{L⊤∞,q*} ≤ 1` by the attained case of Hölder (`NNReal.isGreatest_Lp`, endpoints apart).
With `Y = y σᵀ`, `tr(Gᵀ Y) = yᵀ G σ = (Hᵀ y)ᵀ β ≤ ‖β‖_q` for the minimal `β` with `H β = G σ`,
by Hölder, so `LR_q ≤` the norm of `G σ` `≤ r ≤ LR_q`. `q* = q'` is the Hölder conjugate.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal NNReal
open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A `PiLp` norm is the `q`-norm of the components' norms. -/
theorem aux_lrExact_norm_eq {β : Fin l → Type*} [∀ i, SeminormedAddCommGroup (β i)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (x : PiLp q β) :
    ‖x‖ = ‖WithLp.toLp q (fun i => ‖x i‖)‖ := by -- --- PROOF ---
  by_cases hq : q = ∞
  · subst hq
    simp [PiLp.norm_eq_ciSup]
  · have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    simp [PiLp.norm_eq_sum hq0]

/-- The `q`-norm is monotone in the absolute values of the entries. -/
theorem aux_lrExact_norm_mono (q : ℝ≥0∞) [Fact (1 ≤ q)] (a b : Fin l → ℝ)
    (h : ∀ i, |a i| ≤ b i) : ‖WithLp.toLp q a‖ ≤ ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  have hb : ∀ i, 0 ≤ b i := fun i => (abs_nonneg _).trans (h i)
  by_cases hq : q = ∞
  · subst hq
    simp only [PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact (h i).trans ((le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm b i))
  · have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    rw [PiLp.norm_eq_sum hq0, PiLp.norm_eq_sum hq0]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    simp only [Real.norm_eq_abs]
    exact Real.rpow_le_rpow (abs_nonneg _) ((h i).trans (le_abs_self _)) hq0.le

/-- Hölder: `Σ aᵢ bᵢ ≤ ‖a‖_{q'} ‖b‖_q`, endpoints included. -/
theorem aux_lrExact_holder (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q'] (a b : Fin l → ℝ) :
    ∑ i, a i * b i ≤ ‖WithLp.toLp q' a‖ * ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  by_cases hq : q = ∞
  · -- `q' = 1`
    have hq' : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q q').mp hq
    subst hq hq'
    rw [PiLp.norm_eq_of_L1, PiLp.norm_toLp, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Real.norm_eq_abs]
    calc a i * b i ≤ |a i| * |b i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |a i| * ‖b‖ := mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i) (abs_nonneg _)
  by_cases hq1 : q = 1
  · -- `q' = ∞`
    have hq' : q' = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q' q).mpr hq1
    subst hq1 hq'
    rw [PiLp.norm_eq_of_L1, PiLp.norm_toLp, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Real.norm_eq_abs]
    calc a i * b i ≤ |a i| * |b i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ ‖a‖ * |b i| := mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i) (abs_nonneg _)
  · -- `1 < q < ∞`: the real Hölder inequality
    have hq'1 : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1
    have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hq'0 : 0 < q'.toReal :=
      ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hq'1
    have hR : q'.toReal.HolderConjugate q.toReal := by
      simpa using ENNReal.HolderTriple.toReal 1 hq'0 hq0
    rw [PiLp.norm_eq_sum hq'0, PiLp.norm_eq_sum hq0]
    simpa [Real.norm_eq_abs] using Real.inner_le_Lp_mul_Lq Finset.univ a b hR

/-- The converse for `u ≥ 0`: `Σ wᵢ uᵢ ≤ ‖w‖_q` for every `w ≥ 0` gives `‖u‖_{q'} ≤ 1`. -/
theorem aux_lrExact_dual_le_one (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (u : Fin l → ℝ) (hu : ∀ i, 0 ≤ u i)
    (h : ∀ w : Fin l → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i * u i ≤ ‖WithLp.toLp q w‖) :
    ‖WithLp.toLp q' u‖ ≤ 1 := by -- --- PROOF ---
  by_cases hq : q = ∞
  · -- `q' = 1`: test with `w = 1`
    have hq' : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q q').mp hq
    subst hq hq'
    have h1 := h 1 (fun _ => zero_le_one)
    simp only [Pi.one_apply, one_mul, PiLp.norm_toLp] at h1
    rw [PiLp.norm_eq_of_L1]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hu _)]
    exact h1.trans ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp)
  by_cases hq1 : q = 1
  · -- `q' = ∞`: test with the unit vectors
    have hq' : q' = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q' q).mpr hq1
    subst hq1 hq'
    rw [PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    have h1 := h (Pi.single i 1) (fun j => by by_cases hj : j = i <;> simp [hj])
    have hs : ‖WithLp.toLp 1 (Pi.single (M := fun _ : Fin l => ℝ) i 1)‖ = 1 := by
      rw [PiLp.norm_eq_of_L1]
      simp [Pi.single_apply, apply_ite]
    rw [hs] at h1
    simpa [Pi.single_apply, Real.norm_eq_abs, abs_of_nonneg (hu i)] using h1
  · -- `1 < q < ∞`: the maximizer of `NNReal.isGreatest_Lp`
    have hq'1 : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1
    have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hq'0 : 0 < q'.toReal :=
      ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hq'1
    have hR : q'.toReal.HolderConjugate q.toReal := by
      simpa using ENNReal.HolderTriple.toReal 1 hq'0 hq0
    obtain ⟨g, hg, hgeq⟩ := (NNReal.isGreatest_Lp Finset.univ (fun i => (u i).toNNReal) hR).1
    simp only [Set.mem_setOf_eq] at hg
    -- `‖u‖_{q'} = Σ gᵢ uᵢ ≤ ‖g‖_q ≤ 1`
    have h1 := h (fun i => g i) (fun i => (g i).2)
    have hL : (∑ i, ‖u i‖ ^ q'.toReal) ^ (1 / q'.toReal) = ∑ i, (g i : ℝ) * u i := by
      have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hgeq
      push_cast [Real.coe_toNNReal _ (hu _)] at this
      simp only [Real.norm_eq_abs, abs_of_nonneg (hu _)]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [PiLp.norm_eq_sum hq'0, hL]
    refine h1.trans ?_
    rw [PiLp.norm_eq_sum hq0]
    refine Real.rpow_le_one (Finset.sum_nonneg fun i _ => by positivity) ?_ (by positivity)
    have := NNReal.coe_le_coe.mpr hg
    push_cast at this
    simpa [Real.norm_eq_abs] using this

/-- The same for matrices: a functional `X ↦ Σ Zᵢⱼ Xᵢⱼ` of `L⊤₁,q`-norm at most `1` has
`‖Z‖_{L⊤∞,q'} ≤ 1`. -/
theorem aux_lrExact_matrix_dual_le_one (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (Z : Matrix (Fin l) (Fin m) ℝ)
    (h : ∀ X : Matrix (Fin l) (Fin m) ℝ,
      ∑ i, ∑ j, Z i j * X i j ≤ ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖) :
    ‖WithLp.toLp q' (fun i => ⨆ j, |Z i j|)‖ ≤ 1 := by -- --- PROOF ---
  refine aux_lrExact_dual_le_one q q' _ (fun i => Real.iSup_nonneg fun j => abs_nonneg _)
    fun w hw => ?_
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · simp only [Real.iSup_of_isEmpty, mul_zero, Finset.sum_const_zero]
    exact norm_nonneg _
  -- a largest entry `J i` in each row, and `X` its sign times `w i` there
  choose J hJ using fun i =>
    Finset.exists_max_image Finset.univ (fun j => |Z i j|) Finset.univ_nonempty
  have hsup : ∀ i, (⨆ j, |Z i j|) = |Z i (J i)| := fun i =>
    le_antisymm (ciSup_le fun j => (hJ i).2 j (Finset.mem_univ j))
      (le_ciSup (f := fun j => |Z i j|) (Set.finite_range _).bddAbove (J i))
  set X : Matrix (Fin l) (Fin m) ℝ := fun i j => if j = J i then w i * SignType.sign (Z i j) else 0
  have hrow : ∀ i, ∑ j, Z i j * X i j = w i * |Z i (J i)| := fun i => by
    simp only [X, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_left_comm, self_mul_sign]
  have hnorm : ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖ ≤ ‖WithLp.toLp q w‖ :=
    aux_lrExact_norm_mono q _ _ fun i => by
      simp only [X, apply_ite, abs_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, abs_mul,
        abs_of_nonneg (hw i)]
      rw [abs_abs]
      exact mul_le_of_le_one_right (hw i) (by
        rcases lt_trichotomy (Z i (J i)) 0 with hz | hz | hz <;> simp [hz])
  simp only [hsup]
  calc ∑ i, w i * |Z i (J i)| = ∑ i, ∑ j, Z i j * X i j := by simp only [hrow]
    _ ≤ _ := h X
    _ ≤ _ := hnorm

/-- `tr(Aᵀ B) = Σₖ Σⱼ A_{kj} B_{kj}`. -/
theorem aux_lrExact_trace {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ) :
    trace (Aᵀ * B) = ∑ k, ∑ j, A k j * B k j := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

/-- A functional on matrices is `M ↦ Σ M_{kj} f(E_{kj})`. -/
theorem aux_lrExact_functional_eq (f : Matrix (Fin n) (Fin m) ℝ →ₗ[ℝ] ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) :
    f M = ∑ k, ∑ j, M k j * f (single k j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single k j (M k j) = M k j • single k j (1 : ℝ) by simp, map_smul, smul_eq_mul]

/-- After `X ↦ H X`, it is `X ↦ Σ (Hᵀ Z)_{ij} X_{ij}` with `Z_{kj} = f(E_{kj})`. -/
theorem aux_lrExact_functional_mul (f : Matrix (Fin n) (Fin m) ℝ →ₗ[ℝ] ℝ)
    (H : Matrix (Fin n) (Fin l) ℝ) (X : Matrix (Fin l) (Fin m) ℝ) :
    f (H * X) = ∑ i, ∑ j,
      (Hᵀ * Matrix.of fun k j => f (single k j (1 : ℝ))) i j * X i j := by -- --- PROOF ---
  -- both sides are `tr((H X)ᵀ Z) = tr(Xᵀ (Hᵀ Z))`
  rw [aux_lrExact_functional_eq f]
  have h := aux_lrExact_trace (H * X) (Matrix.of fun k j => f (single k j (1 : ℝ)))
  rw [transpose_mul, Matrix.mul_assoc, aux_lrExact_trace] at h
  simp only [of_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem lr_exact_of_columns_eq_up_to_sign (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ) (Y : Matrix (Fin n) (Fin m) ℝ)
    (hY : ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Y) i j|)‖ ≤ 1)
    (hYmax : ∀ Y' : Matrix (Fin n) (Fin m) ℝ,
      ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Y') i j|)‖ ≤ 1 → trace (Gᵀ * Y') ≤ trace (Gᵀ * Y))
    (hcol : ∀ j j', (fun k => Y k j) = (fun k => Y k j') ∨
      (fun k => Y k j) = -(fun k => Y k j')) :
    ∃ LR, IsLeast {N | ∃ X : Matrix (Fin l) (Fin m) ℝ, H * X = G ∧
        N = ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖} LR ∧
      IsGreatest ((fun α => coeffNorm ((Matrix.mulVecLin H) ∘ₗ
        (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ α)) ''
        Metric.closedBall 0 1) LR := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  set L := mulLeftLinearMap (Fin m) ℝ H with hL
  -- a maximizer puts `G` in the range of `X ↦ H X`: else `Y + t Z` is unbounded
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, H * X₀ = G := by
    by_contra hne
    have hG : G ∉ LinearMap.range L := fun ⟨X, hX⟩ => hne ⟨X, hX⟩
    obtain ⟨f, hfG, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hG inferInstance
    set Z : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun k j => f (single k j 1)
    have hHZ : Hᵀ * Z = 0 := by
      ext i j
      have h0 : f (H * single i j (1 : ℝ)) = 0 := by
        have : f (L (single i j 1)) ∈ (LinearMap.range L).map f := ⟨_, ⟨_, rfl⟩, rfl⟩
        rw [hf] at this
        simpa [L] using (Submodule.mem_bot ℝ).mp this
      rw [aux_lrExact_functional_mul f H] at h0
      simpa [single_apply, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq] using h0
    have hfeas := hYmax (Y + (f G)⁻¹ • Z) (by
      rwa [Matrix.mul_add, Matrix.mul_smul, hHZ, smul_zero, add_zero])
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, aux_lrExact_trace G Z] at hfeas
    have hGZ : ∑ k, ∑ j, G k j * Z k j = f G := (aux_lrExact_functional_eq f G).symm
    rw [hGZ, smul_eq_mul, inv_mul_cancel₀ hfG] at hfeas
    linarith
  -- `ℝ^{l×m}` normed by `‖·‖_{L⊤₁,q}`, and `X ↦ H X` on it
  let J : (Fin l → Fin m → ℝ) ≃ₗ[ℝ] PiLp q (fun _ : Fin l => PiLp 1 (fun _ : Fin m => ℝ)) :=
    (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 1 ℝ (Fin m → ℝ)).symm).trans
      (WithLp.linearEquiv q ℝ _).symm
  have hJ : ∀ X : Matrix (Fin l) (Fin m) ℝ,
      ‖J X‖ = ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖ := fun X => by
    rw [aux_lrExact_norm_eq]
    congr 2
    funext i
    simp [J, PiLp.norm_eq_of_L1]
  set Lₑ := L ∘ₗ J.symm.toLinearMap
  have hLJ : ∀ X : Matrix (Fin l) (Fin m) ℝ, Lₑ (J X) = H * X := fun X => by
    change H * Matrix.of (J.symm (J X)) = H * X
    rw [J.symm_apply_apply]
    rfl
  set K := LinearMap.ker Lₑ
  have hKc : IsClosed (K : Set (PiLp q (fun _ : Fin l => PiLp 1 (fun _ : Fin m => ℝ)))) :=
    Submodule.closed_of_finiteDimensional K
  set x₀ := J X₀
  have hLx₀ : Lₑ x₀ = G := (hLJ X₀).trans hX₀
  -- `LR_q` is the distance from `x₀` to `K`, attained
  set d := Metric.infDist x₀ K
  have hd : ∀ x, Lₑ x = G → d ≤ ‖x‖ := fun x hx => by
    have hmem : x₀ - x ∈ K := by simp [K, hLx₀, hx]
    calc d ≤ dist x₀ (x₀ - x) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖x‖ := by rw [dist_eq_norm, sub_sub_cancel]
  obtain ⟨k, hk, hkd⟩ := hKc.exists_infDist_eq_dist ⟨0, K.zero_mem⟩ x₀
  set Xs : Matrix (Fin l) (Fin m) ℝ := J.symm (x₀ - k)
  have hXs : H * Xs = G := by
    rw [← hLJ, J.apply_symm_apply, map_sub, hLx₀, LinearMap.mem_ker.mp hk, sub_zero]
  have hXsd : ‖WithLp.toLp q (fun i => ∑ j, |Xs i j|)‖ = d := by
    rw [← hJ, J.apply_symm_apply, ← dist_eq_norm, ← hkd]
  -- Hahn–Banach on the quotient by `K`
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ (K.mkQ x₀)
  have hdq : d ≤ ‖K.mkQ x₀‖ := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨x, hx, hxn⟩ := Submodule.Quotient.norm_mk_lt (K.mkQ x₀) hε
    refine (hd x ?_).trans_lt hxn
    have : x - x₀ ∈ K := (Submodule.Quotient.eq K).mp hx
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    rw [this, hLx₀]
  set φ : Module.Dual ℝ (PiLp q (fun _ : Fin l => PiLp 1 (fun _ : Fin m => ℝ))) :=
    (g : (_ ⧸ K) →ₗ[ℝ] ℝ) ∘ₗ K.mkQ
  have hφ : ∀ x, φ x ≤ ‖x‖ := fun x => by
    calc φ x ≤ ‖g (K.mkQ x)‖ := le_abs_self _
      _ ≤ ‖g‖ * ‖K.mkQ x‖ := g.le_opNorm _
      _ ≤ 1 * ‖x‖ := mul_le_mul hg1 (Submodule.Quotient.norm_mk_le K x) (norm_nonneg _)
          zero_le_one
      _ = ‖x‖ := one_mul _
  have hφK : φ ∈ K.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    simp [φ, (Submodule.Quotient.mk_eq_zero K).mpr hw]
  -- it factors through `X ↦ H X`: `φ(X) = tr(Y*ᵀ H X)`, and `Y*` is feasible
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφK
  obtain ⟨ψ, hψ⟩ := hφK
  set Ys : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun k j => ψ (single k j 1)
  have hφX : ∀ X, φ (J X) = ∑ i, ∑ j, (Hᵀ * Ys) i j * X i j := fun X => by
    rw [← hψ, LinearMap.dualMap_apply, hLJ]
    exact aux_lrExact_functional_mul ψ H X
  have hYs : ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Ys) i j|)‖ ≤ 1 :=
    aux_lrExact_matrix_dual_le_one q q' _ fun X => by
      rw [← hφX, ← hJ]
      exact hφ _
  have hdY : d ≤ trace (Gᵀ * Y) := by
    refine le_trans ?_ (hYmax Ys hYs)
    have h1 : ∑ k, ∑ j, G k j * Ys k j = ψ G := (aux_lrExact_functional_eq ψ G).symm
    have h2 : ψ G = φ x₀ := by rw [← hψ, LinearMap.dualMap_apply, hLx₀]
    have h3 : φ x₀ = ‖K.mkQ x₀‖ := hgx
    rw [aux_lrExact_trace, h1, h2, h3]
    exact hdq
  -- `Y = y σᵀ`
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, ∀ j, (fun k => Y k j) = y ∨ (fun k => Y k j) = -y := by
    rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨j₀⟩⟩
    · exact ⟨0, fun j => isEmptyElim j⟩
    · exact ⟨fun k => Y k j₀, fun j => hcol j j₀⟩
  set σ : Fin m → ℝ := fun j => if (fun k => Y k j) = y then 1 else -1
  have hYσ : ∀ k j, Y k j = σ j * y k := fun k j => by
    by_cases h : (fun k => Y k j) = y
    · simp only [σ, h, if_true, one_mul]
      exact congrFun h k
    · have := congrFun ((hy j).resolve_left h) k
      simp only [σ, h, if_false, neg_one_mul]
      simpa using this
  -- `σ` is a sign vector, a corner of the cube
  have hσ1 : ∀ j, |σ j| = 1 := fun j => by
    simp only [σ]
    split_ifs <;> simp
  have hσ : σ ∈ Metric.closedBall (0 : Fin m → ℝ) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by rw [Real.norm_eq_abs, hσ1]
  -- every `G α` on the cube has the preimage `Xs α`
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  have hHl : ∀ β, Hl β = H *ᵥ WithLp.ofLp β := fun β => rfl
  have hup : ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, coeffNorm Hl (G *ᵥ α) ≤ d :=
    fun α hα => by
    rw [mem_closedBall_zero_iff] at hα
    have hGα : G *ᵥ α = Hl (WithLp.toLp q (Xs *ᵥ α)) := by
      rw [hHl, WithLp.ofLp_toLp, mulVec_mulVec, hXs]
    rw [hGα, ← hXsd]
    refine (coeffNorm_le Hl _).trans (aux_lrExact_norm_mono q _ _ fun i => ?_)
    rw [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) ((norm_le_pi_norm α j).trans hα)
  -- `tr(Gᵀ Y) = (Hᵀ y)ᵀ β ≤ ‖β‖_q` for the minimal `β` with `H β = G σ`
  have hlow : trace (Gᵀ * Y) ≤ coeffNorm Hl (G *ᵥ σ) := by
    rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨j₀⟩⟩
    · rw [aux_lrExact_trace]
      simpa using coeffNorm_nonneg Hl (G *ᵥ σ)
    obtain ⟨β, hβ, hβn⟩ := exists_coeffNorm_eq Hl ⟨WithLp.toLp q (X₀ *ᵥ σ), by
      rw [hHl, WithLp.ofLp_toLp, mulVec_mulVec, hX₀]⟩
    have htr : trace (Gᵀ * Y) = ∑ i, (y ᵥ* H) i * WithLp.ofLp β i := by
      calc trace (Gᵀ * Y) = y ⬝ᵥ (G *ᵥ σ) := by
            rw [aux_lrExact_trace]
            simp only [hYσ, dotProduct, mulVec, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
        _ = y ⬝ᵥ (H *ᵥ WithLp.ofLp β) := by rw [← hHl, hβ]
        _ = (y ᵥ* H) ⬝ᵥ WithLp.ofLp β := dotProduct_mulVec _ _ _
        _ = _ := rfl
    have hrow : ∀ i j, (Hᵀ * Y) i j = σ j * (y ᵥ* H) i := fun i j => by
      simp only [mul_apply, transpose_apply, hYσ, vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    -- Eq. 36: the rows of `Hᵀ Y` are `σᵀ` times `(Hᵀ y)ᵢ`, so `‖Hᵀ y‖_{q'} ≤ 1`
    have h1 : ‖WithLp.toLp q' (y ᵥ* H)‖ ≤ 1 := by
      refine (aux_lrExact_norm_mono q' _ _ fun i => ?_).trans hY
      refine le_trans ?_ (le_ciSup (f := fun j => |(Hᵀ * Y) i j|) (Set.finite_range _).bddAbove j₀)
      rw [hrow, abs_mul, hσ1, one_mul]
    rw [htr, ← hβn]
    refine (aux_lrExact_holder q q' _ _).trans ?_
    calc _ ≤ 1 * ‖WithLp.toLp q (WithLp.ofLp β)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖β‖ := by simp
  -- `LR_q = d ≤ tr(Gᵀ Y) ≤ ‖G σ‖ ≤ r ≤ LR_q`
  have hσd : coeffNorm Hl (G *ᵥ σ) = d := le_antisymm (hup σ hσ) (hdY.trans hlow)
  refine ⟨d, ⟨⟨Xs, hXs, hXsd.symm⟩, ?_⟩, ⟨⟨σ, hσ, hσd⟩, ?_⟩⟩
  · rintro _ ⟨X, hX, rfl⟩
    rw [← hJ]
    exact hd _ (by rw [hLJ, hX])
  · rintro _ ⟨α, hα, rfl⟩
    exact hup α hα

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
