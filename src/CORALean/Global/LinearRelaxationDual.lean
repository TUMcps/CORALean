module

public import CORALean.Global.MatrixFunctionalMulEqSum
public import CORALean.Global.PiLpNormToLpLeOfAbsLe
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# The linear relaxation has a dual certificate

The strong duality behind [1, Thm. 15 (accuracy)] (Eq. 32, which [1] takes from its reference
22): when some `X` has `H X = G`, the minimum `LR_q(G, H) = min_{HX = G} ‖X‖_{L⊤₁,q}` (Eq. 29)
is attained, and some `Y` with `‖Hᵀ Y‖_{L⊤∞,q*} ≤ 1` has `tr(Gᵀ Y) ≥ LR_q(G, H)`. On
`ℝ^{l×m}` normed by `‖·‖_{L⊤₁,q}` (a `PiLp q` of `PiLp 1`), `LR_q` is the distance from a
feasible point to the kernel `K` of `X ↦ H X`; a functional of norm `≤ 1` on the quotient by `K`
attains it (Hahn–Banach), it factors through `X ↦ H X` as `X ↦ tr(Yᵀ H X)`, and its norm bound
gives `‖Hᵀ Y‖_{L⊤∞,q*} ≤ 1` by the attained case of Hölder. The proof of [1, Thm. 16]
(`lr_exact_of_columns_eq_up_to_sign`) uses it too; `q* = q'` is the Hölder conjugate.

## Inputs
* `q` – exponent of the coefficient norm
* `q'` – its conjugate exponent
* `G` – zonotope generator matrix
* `H` – ellipsotope generator matrix

## Hypotheses
* `hG` – some coefficient matrix maps onto the zonotope generators

## Conclusion
* the relaxation value is attained and a dual matrix of unit norm reaches it

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

/-- A `PiLp` norm is the `q`-norm of the components' norms. -/
private theorem aux_lrDual_norm_eq {β : Fin l → Type*} [∀ i, SeminormedAddCommGroup (β i)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (x : PiLp q β) : -- --- CONCL ---
    ‖x‖ = ‖WithLp.toLp q (fun i => ‖x i‖)‖ := by -- --- PROOF ---
  by_cases hq : q = ∞
  · subst hq
    simp [PiLp.norm_eq_ciSup]
  · have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    simp [PiLp.norm_eq_sum hq0]

/-- The converse for `u ≥ 0`: `Σ wᵢ uᵢ ≤ ‖w‖_q` for every `w ≥ 0` gives `‖u‖_{q'} ≤ 1`. -/
private theorem aux_lrDual_dual_le_one (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (u : Fin l → ℝ) (hu : ∀ i, 0 ≤ u i)
    (h : ∀ w : Fin l → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i * u i ≤ ‖WithLp.toLp q w‖) : -- --- CONCL ---
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
private theorem aux_lrDual_matrix_dual_le_one (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (Z : Matrix (Fin l) (Fin m) ℝ)
    (h : ∀ X : Matrix (Fin l) (Fin m) ℝ,
      ∑ i, ∑ j, Z i j * X i j ≤ ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖) : -- --- CONCL ---
    ‖WithLp.toLp q' (fun i => ⨆ j, |Z i j|)‖ ≤ 1 := by -- --- PROOF ---
  refine aux_lrDual_dual_le_one q q' _ (fun i => Real.iSup_nonneg fun j => abs_nonneg _)
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
    PiLp.norm_toLp_le_of_abs_le q _ _ fun i => by
      simp only [X, apply_ite, abs_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, abs_mul,
        abs_of_nonneg (hw i)]
      rw [abs_abs]
      exact mul_le_of_le_one_right (hw i) (by
        rcases lt_trichotomy (Z i (J i)) 0 with hz | hz | hz <;> simp [hz])
  simp only [hsup]
  calc ∑ i, w i * |Z i (J i)| = ∑ i, ∑ j, Z i j * X i j := by simp only [hrow]
    _ ≤ _ := h X
    _ ≤ _ := hnorm


-- =======================================  MAIN THEOREM  ======================================= --

theorem lr_exists_dual (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hG : ∃ X₀ : Matrix (Fin l) (Fin m) ℝ, H * X₀ = G) : -- --- CONCL ---
    ∃ LR, IsLeast {N | ∃ X : Matrix (Fin l) (Fin m) ℝ, H * X = G ∧
        N = ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖} LR ∧
      ∃ Y : Matrix (Fin n) (Fin m) ℝ,
        ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Y) i j|)‖ ≤ 1 ∧
          LR ≤ trace (Gᵀ * Y) := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  set L := mulLeftLinearMap (Fin m) ℝ H with hL
  obtain ⟨X₀, hX₀⟩ := hG
  -- `ℝ^{l×m}` normed by `‖·‖_{L⊤₁,q}`, and `X ↦ H X` on it
  let J : (Fin l → Fin m → ℝ) ≃ₗ[ℝ] PiLp q (fun _ : Fin l => PiLp 1 (fun _ : Fin m => ℝ)) :=
    (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 1 ℝ (Fin m → ℝ)).symm).trans
      (WithLp.linearEquiv q ℝ _).symm
  have hJ : ∀ X : Matrix (Fin l) (Fin m) ℝ,
      ‖J X‖ = ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖ := fun X => by
    rw [aux_lrDual_norm_eq]
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
    exact functional_mul_eq_sum ψ H X
  have hYs : ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Ys) i j|)‖ ≤ 1 :=
    aux_lrDual_matrix_dual_le_one q q' _ fun X => by
      rw [← hφX, ← hJ]
      exact hφ _
  refine ⟨d, ⟨⟨Xs, hXs, hXsd.symm⟩, ?_⟩, Ys, hYs, ?_⟩
  · rintro _ ⟨X, hX, rfl⟩
    rw [← hJ]
    exact hd _ (by rw [hLJ, hX])
  · have h1 : ∑ k, ∑ j, G k j * Ys k j = ψ G := (functional_eq_sum_single ψ G).symm
    have h2 : ψ G = φ x₀ := by rw [← hψ, LinearMap.dualMap_apply, hLx₀]
    have h3 : φ x₀ = ‖K.mkQ x₀‖ := hgx
    rw [trace_transpose_mul_eq_sum, h1, h2, h3]
    exact hdq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
