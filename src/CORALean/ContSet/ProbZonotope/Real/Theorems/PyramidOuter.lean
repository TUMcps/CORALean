module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Pyramid
public import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GaussPdfLeMaxIff
public import CORALean.ContSet.ProbZonotope.Real.Operations.Max
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawDensity
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

@[expose] public section

/-!
# The pyramid bounds the probability of a set, up to its floor

Every law `N(μ, Σ)` of a probabilistic zonotope with positive definite covariance has density
at most `max(probZ, mᵢ)` outside `zonotope(probZ, mᵢ)` (`aux_mem_zonotope_of_quad_lt`) and at most
the peak everywhere. For a descending `mArray` the layers telescope, and for a set `Q`
`P[X ∈ Q] ≤ maxVal(1) · V(Q) + pyramid(probZ, mArray, Q)`: the density steps times the volumes
of the layers, plus the lowest level over the whole of `Q`. `pyramid` alone, which is what CORA
returns, omits that floor: `pyramid_not_ge_prob` is a set of probability `1` with
`pyramid < 1`. Outer, up to the floor: not an enclosure of the probability by `pyramid` itself.

## Inputs
* `P` – probabilistic zonotope
* `k` – natural number
* `mArray` – real numbers indexed by `Fin k`
* `Q` – set of points
* `ν` – measure

## Hypotheses
* `hP` – `P.cov.PosDef`
* `h0` – the entries of `mArray` are nonnegative
* `hanti` – `Antitone mArray`
* `hν` – `ν ∈ P.laws`

## Conclusion
* the pyramid bounds the probability of a set, up to its floor
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp Matrix
open scoped MatrixOrder ENNReal

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A mean plus the covariance's square root applied to a cube lies in the confidence set. -/
theorem ProbZonotope.aux_add_sqrt_mulVec_mem_zonotope (P : ProbZonotope n) {μ : Vec ℝ n}
    (hμ : μ ∈ P.Z.construct) {m : ℝ} (hm : 0 < m) {β : Vec ℝ n}
    (hβ : ∀ j, |β j| ≤ m) : -- --- CONCL ---
    μ + CFC.sqrt P.cov *ᵥ β ∈ (P.zonotope m).construct := by -- --- PROOF ---
  rw [ProbZonotope.zonotope, ← Zonotope.plus_exact]
  refine Set.add_mem_add hμ ⟨fun j => β j / m, fun j => ?_, ?_⟩
  · rw [abs_div, abs_of_pos hm, div_le_one hm]
    exact hβ j
  · funext i
    simp only [confidenceZonotope, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    change CFC.sqrt P.cov i j * β j = β j / m * (m * CFC.sqrt P.cov i j)
    field_simp


/-- The open `m`-sigma ellipsoid around a mean lies in the confidence set. -/
theorem ProbZonotope.aux_mem_zonotope_of_quad_lt (P : ProbZonotope n) (hP : P.cov.PosDef)
    {μ : Vec ℝ n} (hμ : μ ∈ P.Z.construct) {m : ℝ} (hm : 0 ≤ m) {y : Vec ℝ n}
    (hy : (y - μ) ⬝ᵥ P.cov⁻¹ *ᵥ (y - μ) < m ^ 2) : -- --- CONCL ---
    y ∈ (P.zonotope m).construct := by -- --- PROOF ---
  -- the symmetric square root `B` of the covariance, invertible
  set B := CFC.sqrt P.cov with hBdef
  have hBB : B * B = P.cov := CFC.sqrt_mul_sqrt_self P.cov hP.posSemidef.nonneg
  have hBt : Bᵀ = B := by
    have := (CFC.sqrt_nonneg P.cov).isSelfAdjoint
    simpa [IsSelfAdjoint, star_eq_conjTranspose] using this
  have hdet : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBB
    rw [det_mul, h0, zero_mul] at this
    exact hP.det_pos.ne this
  have hBu : IsUnit B := (isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hdet)
  set d := y - μ with hd
  set u := B⁻¹ *ᵥ d with hu
  have hBinv_t : (B⁻¹)ᵀ = B⁻¹ := by rw [transpose_nonsing_inv, hBt]
  -- the quadratic form is the squared norm of `u`
  have hvm : d ᵥ* B⁻¹ = B⁻¹ *ᵥ d := by
    conv_lhs => rw [← hBinv_t]
    exact vecMul_transpose _ _
  have hq : d ⬝ᵥ P.cov⁻¹ *ᵥ d = u ⬝ᵥ u := by
    rw [← hBB, Matrix.mul_inv_rev, ← mulVec_mulVec, dotProduct_mulVec, hu, hvm]
  rw [hq] at hy
  -- `m` is positive, as `‖u‖² < m²`
  have hm2 : 0 < m := by
    rcases hm.eq_or_lt with h | h
    · rw [← h] at hy
      exact absurd hy (not_lt.2 (by simpa using dotProduct_self_star_nonneg u))
    · exact h
  -- every coefficient of `u` is within `m`, so `y = μ + B u` is in the confidence set
  have hcoef : ∀ j, |u j| ≤ m := fun j => by
    have h1 : u j ^ 2 ≤ u ⬝ᵥ u := by
      rw [dotProduct]
      simpa [sq] using Finset.single_le_sum (f := fun i => u i * u i)
        (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ j)
    exact abs_le_of_sq_le_sq (by nlinarith) hm2.le
  have key := P.aux_add_sqrt_mulVec_mem_zonotope hμ hm2 hcoef
  have hy' : y = μ + B *ᵥ u := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).1 hBu), one_mulVec, hd]
    abel
  rw [hy']
  exact key


section
open scoped _root_.Real

/-- `ProbZonotope.max` falls with `m`. -/
theorem ProbZonotope.aux_max_anti (P : ProbZonotope n) (hd : 0 ≤ P.cov.det) {m m' : ℝ}
    (h0 : 0 ≤ m) (h : m ≤ m') : -- --- CONCL ---
    P.max m' ≤ P.max m := by -- --- PROOF ---
  unfold ProbZonotope.max
  have hK : 0 ≤ 1 / ((2 * π) ^ ((n : ℝ) / 2) * P.cov.det ^ ((1 : ℝ) / 2)) := by
    have : 0 < 2 * π := by positivity
    positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
  nlinarith

end


section
open Finset

/-- A value below every level that fails is below the telescoped layers. -/
theorem aux_le_add_sum_levels : -- --- CONCL ---
    ∀ {k : ℕ} (L : Fin (k + 1) → ℝ) (p : Fin k → Prop)
    [DecidablePred p] (v : ℝ), (∀ i : Fin k, L i.castSucc ≤ L i.succ) →
    (∀ i, ¬ p i → v ≤ L i.castSucc) → v ≤ L (Fin.last k) →
    v ≤ L 0 + ∑ i, if p i then L i.succ - L i.castSucc else 0 := by -- --- PROOF ---
  intro k
  -- induction on the number of layers
  induction k with
  | zero =>
    intro L p _ v _ _ hlast
    simpa using hlast
  | succ k ih =>
    intro L p _ v hmono hnot hlast
    -- the sum of non-negative steps is non-negative
    have hnn : 0 ≤ ∑ i : Fin (k + 1), if p i then L i.succ - L i.castSucc else 0 :=
      Finset.sum_nonneg fun i _ => by
        split_ifs
        · linarith [hmono i]
        · exact le_rfl
    -- peel layer `0`: in it, the claim for the shifted levels; out of it, `v ≤ L 0`
    by_cases h0 : p 0
    · have key := ih (fun i => L i.succ) (fun i => p i.succ) v (fun i => hmono i.succ)
        (fun i hi => hnot i.succ hi) hlast
      rw [Fin.sum_univ_succ]
      simp only [h0, if_true, Fin.succ_zero_eq_one, Fin.castSucc_zero]
      simp only [Fin.succ_zero_eq_one, Fin.succ_castSucc] at key
      linarith
    · have := hnot 0 h0
      simp only [Fin.castSucc_zero] at this
      linarith

end


theorem aux_measurableSet_image_zonotope (P : ProbZonotope n) (m : ℝ) :
    MeasurableSet (toLp 2 '' (P.zonotope m).construct : Set (EuclideanSpace ℝ (Fin n))) :=
  (((P.zonotope m).isCompact_construct.image (PiLp.continuous_toLp 2 _)).isClosed).measurableSet

theorem aux_volume_image_zonotope_lt_top (P : ProbZonotope n) (m : ℝ) :
    volume (toLp 2 '' (P.zonotope m).construct : Set (EuclideanSpace ℝ (Fin n))) < ⊤ :=
  ((P.zonotope m).isCompact_construct.image (PiLp.continuous_toLp 2 _)).measure_lt_top


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.pyramid_outer (P : ProbZonotope n) (hP : P.cov.PosDef) {k : ℕ}
    {mArray : Fin k → ℝ} (h0 : ∀ i, 0 ≤ mArray i) (hanti : Antitone mArray)
    (Q : Set (EuclideanSpace ℝ (Fin n))) {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : ν ∈ P.laws) : -- --- CONCL ---
    ν Q ≤ ENNReal.ofReal (P.pyramidLevels mArray 0) * volume Q
      + ENNReal.ofReal (P.pyramid mArray Q) := by -- --- PROOF ---
  classical
  obtain ⟨μ, hμ, rfl⟩ := hν
  have hdet : 0 < P.cov.det := hP.det_pos
  -- the law as a density
  set B := CFC.sqrt P.cov with hBdef
  have hBB : B * B = P.cov := CFC.sqrt_mul_sqrt_self P.cov hP.posSemidef.nonneg
  have hBt : Bᵀ = B := by
    have := (CFC.sqrt_nonneg P.cov).isSelfAdjoint
    simpa [IsSelfAdjoint, star_eq_conjTranspose] using this
  have hdens : multivariateGaussian (toLp 2 μ) P.cov
      = volume.withDensity (fun x => ENNReal.ofReal (gaussPdf μ P.cov x)) := by
    have hlaw : multivariateGaussian (toLp 2 μ) P.cov = gZonotopeLaw μ B := by
      rw [gZonotopeLaw_eq, hBt, hBB]
    have hG : (B * Bᵀ).det ≠ 0 := by rw [hBt, hBB]; exact hdet.ne'
    rw [hlaw, gZonotopeLaw_eq_withDensity_gaussPdf μ B hG, hBt, hBB]
  rw [hdens]
  -- the layers
  set L := P.pyramidLevels mArray with hL
  set Z : Fin k → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => toLp 2 '' (P.zonotope (mArray i)).construct with hZ
  have hLc : ∀ i : Fin k, L i.castSucc = P.max (mArray i) := fun i => by
    simp [hL, ProbZonotope.pyramidLevels]
  have hLl : L (Fin.last k) = P.max 0 := by simp [hL, ProbZonotope.pyramidLevels]
  have hL0 : ∀ j, 0 ≤ L j := fun j => by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [hLl]; unfold ProbZonotope.max; positivity
    · rw [hLc]; unfold ProbZonotope.max; positivity
  -- the steps are non-negative
  have hΔ : ∀ i : Fin k, L i.castSucc ≤ L i.succ := fun i => by
    by_cases hi : (i : ℕ) + 1 < k
    · have : i.succ = (⟨i + 1, hi⟩ : Fin k).castSucc := Fin.ext rfl
      rw [this, hLc, hLc]
      exact P.aux_max_anti hdet.le (h0 _) (hanti (Fin.mk_le_mk.2 (Nat.le_succ _)))
    · have : i.succ = Fin.last k := Fin.ext (by have := i.isLt; simp; omega)
      rw [this, hLl, hLc]
      exact P.aux_max_anti hdet.le le_rfl (h0 i)
  -- pointwise, the density is below the floor plus the steps of the layers the point is in
  have hq0 : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ (ofLp x - μ) ⬝ᵥ P.cov⁻¹ *ᵥ (ofLp x - μ) := fun x =>
    hP.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n), gaussPdf μ P.cov x
      ≤ L 0 + ∑ i, if x ∈ Z i then L i.succ - L i.castSucc else 0 := fun x => by
    refine aux_le_add_sum_levels L (fun i => x ∈ Z i) _ hΔ (fun i hi => ?_) ?_
    · rw [hLc]
      refine (P.gaussPdf_le_max_iff hdet μ x (mArray i)).2 ?_
      by_contra hlt
      refine hi ⟨ofLp x, ?_, by simp⟩
      exact P.aux_mem_zonotope_of_quad_lt hP hμ (h0 i) (not_le.1 hlt)
    · rw [hLl]
      exact (P.gaussPdf_le_max_iff hdet μ x 0).2 (by simpa using hq0 x)
  -- the same in `ℝ≥0∞`, the steps as indicators of their layers
  have hpt' : ∀ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (gaussPdf μ P.cov x)
      ≤ ENNReal.ofReal (L 0)
        + ∑ i, (Z i).indicator (fun _ => ENNReal.ofReal (L i.succ - L i.castSucc)) x := fun x => by
    refine (ENNReal.ofReal_le_ofReal (hpt x)).trans ?_
    have hnn : ∀ i : Fin k, 0 ≤ (if x ∈ Z i then L i.succ - L i.castSucc else 0) := fun i => by
      split_ifs
      · linarith [hΔ i]
      · exact le_rfl
    rw [ENNReal.ofReal_add (hL0 0) (Finset.sum_nonneg fun i _ => hnn i),
      ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i]
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
    by_cases hx : x ∈ Z i <;> simp [hx]
  -- integrate over `Q`: the floor times `V(Q)`, then each layer's step times `V(layer ∩ Q)`
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => aux_measurableSet_image_zonotope P _
  calc volume.withDensity (fun x => ENNReal.ofReal (gaussPdf μ P.cov x)) Q
      = ∫⁻ x in Q, ENNReal.ofReal (gaussPdf μ P.cov x) := withDensity_apply' _ _
    -- the pointwise bound, integrated
    _ ≤ ∫⁻ x in Q, (ENNReal.ofReal (L 0)
        + ∑ i, (Z i).indicator (fun _ => ENNReal.ofReal (L i.succ - L i.castSucc)) x) :=
        lintegral_mono hpt'
    -- the integral of a constant and of indicators of measurable layers
    _ = ENNReal.ofReal (L 0) * volume Q
        + ∑ i, ENNReal.ofReal (L i.succ - L i.castSucc) * volume (Z i ∩ Q) := by
        rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
          lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hZm i))]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_indicator_const (hZm i), Measure.restrict_apply (hZm i)]
    -- the volumes are finite, so the sum is `pyramid`
    _ = ENNReal.ofReal (L 0) * volume Q + ENNReal.ofReal (P.pyramid mArray Q) := by
        congr 1
        have hpy : P.pyramid mArray Q
            = ∑ i, (L i.succ - L i.castSucc) * volume.real (Z i ∩ Q) := rfl
        rw [hpy, ENNReal.ofReal_sum_of_nonneg fun i _ =>
          mul_nonneg (sub_nonneg.2 (hΔ i)) measureReal_nonneg]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hv : volume (Z i ∩ Q) ≠ ⊤ :=
          ((measure_mono Set.inter_subset_left).trans_lt
            (aux_volume_image_zonotope_lt_top P (mArray i))).ne
        rw [ENNReal.ofReal_mul (sub_nonneg.2 (hΔ i)), Measure.real,
          ENNReal.ofReal_toReal hv]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
