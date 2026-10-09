import CORALean.ContSet.ProbZonotope.Real.Operations.Pyramid
import CORALean.ContSet.ProbZonotope.Real.Theorems.MemZonotopeOfQuadLt
import CORALean.ContSet.ProbZonotope.Real.Theorems.GaussPdfLeMaxIff
import CORALean.ContSet.ProbZonotope.Real.Theorems.MaxAnti
import CORALean.ContSet.ProbZonotope.Real.Theorems.LeAddSumOfLevels
import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawDensity
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

/-!
# The pyramid bounds the probability of a set, up to its floor

Every law `N(μ, Σ)` of a probabilistic zonotope with positive definite covariance has density
at most `max(probZ, mᵢ)` outside `zonotope(probZ, mᵢ)` (the open `mᵢ`-sigma ellipsoid around
`μ` is inside it, `mem_zonotope_of_quad_lt`) and at most the peak everywhere. For a descending
`mArray` the layers telescope, and for a set `Q`
`P[X ∈ Q] ≤ maxVal(1) · V(Q) + pyramid(probZ, mArray, Q)`:
the density steps times the volumes of the layers, plus the lowest level over the whole of `Q`.
`pyramid` alone, which is what CORA returns, omits that floor: it is the probability mass above
the level `maxVal(1)` only. `pyramid_not_ge_prob` is a set of probability `1` with `pyramid < 1`.
Outer, up to the floor: not an enclosure of the probability by `pyramid` itself.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp Matrix
open scoped MatrixOrder ENNReal

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

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
    (hν : ν ∈ P.laws) :
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
      exact P.max_anti hdet.le (h0 _) (hanti (Fin.mk_le_mk.2 (Nat.le_succ _)))
    · have : i.succ = Fin.last k := Fin.ext (by have := i.isLt; simp; omega)
      rw [this, hLl, hLc]
      exact P.max_anti hdet.le le_rfl (h0 i)
  -- pointwise, the density is below the floor plus the steps of the layers the point is in
  have hq0 : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ (ofLp x - μ) ⬝ᵥ P.cov⁻¹ *ᵥ (ofLp x - μ) := fun x =>
    hP.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n), gaussPdf μ P.cov x
      ≤ L 0 + ∑ i, if x ∈ Z i then L i.succ - L i.castSucc else 0 := fun x => by
    refine le_add_sum_levels L (fun i => x ∈ Z i) _ hΔ (fun i hi => ?_) ?_
    · rw [hLc]
      refine (P.gaussPdf_le_max_iff hdet μ x (mArray i)).2 ?_
      by_contra hlt
      refine hi ⟨ofLp x, ?_, by simp⟩
      exact P.mem_zonotope_of_quad_lt hP hμ (h0 i) (not_le.1 hlt)
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
