module

public import CORALean.ContSet.ProbZonotope.Real.Definitions.GZonotopeLaw
public import CORALean.ContSet.ProbZonotope.Real.Theorems.StdGaussianEqWithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# A G-zonotope with an invertible square generator matrix has a density

For `B` square with `det B ≠ 0`, the law of `c + B N` is Lebesgue measure with density
`φ(B⁻¹(x - c)) / |det B|`, `φ` the standard Gaussian density: the change of variables
`x = c + Bβ`, whose Jacobian `|det B|` is Mathlib's image of Lebesgue measure under a matrix.
The step from here to [1, Prop. 1]'s density is `GZonotopeLawDensity`.

## Inputs
* `c` – center of length `n`
* `B` – `n × n` matrix

## Hypotheses
* `hB` – `B.det ≠ 0`

## Conclusion
* A G-zonotope with an invertible square generator matrix has a density

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory Matrix WithLp

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `x ↦ c + Bx` maps Lebesgue measure to `|det B|⁻¹` times itself. -/
private theorem aux_map_affine (c : Vec ℝ n) (B : Mat ℝ n n) (hB : B.det ≠ 0) : -- --- CONCL ---
    Measure.map (fun β : EuclideanSpace ℝ (Fin n) => toLp 2 (c + B *ᵥ ofLp β)) volume
      = ENNReal.ofReal |B.det⁻¹| • volume := by -- --- PROOF ---
  have h1 : (fun β : EuclideanSpace ℝ (Fin n) => toLp 2 (c + B *ᵥ ofLp β))
      = (fun x : EuclideanSpace ℝ (Fin n) => toLp 2 c + x) ∘ (toLp 2) ∘ (toLin' B) ∘ (ofLp) := by
    funext β; simp [toLin'_apply]
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    (PiLp.volume_preserving_ofLp (Fin n)).map_eq, Real.map_matrix_volume_pi_eq_smul_volume_pi hB,
    Measure.map_smul, (PiLp.volume_preserving_toLp (Fin n)).map_eq, Measure.map_smul,
    map_add_left_eq_self]


-- =======================================  MAIN THEOREM  ======================================= --

theorem gZonotopeLaw_eq_withDensity (c : Vec ℝ n) (B : Mat ℝ n n)
    (hB : B.det ≠ 0) : -- --- CONCL ---
    gZonotopeLaw c B = volume.withDensity (fun x => ENNReal.ofReal
      (stdGaussPdf n (toLp 2 (B⁻¹ *ᵥ (ofLp x - c))) / |B.det|)) := by -- --- PROOF ---
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun β => toLp 2 (c + B *ᵥ ofLp β)
  have hT : Measurable T := by fun_prop
  have hφ : Measurable (fun y => ENNReal.ofReal (stdGaussPdf n y)) := by
    unfold stdGaussPdf; fun_prop
  have hψ : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (stdGaussPdf n (toLp 2 (B⁻¹ *ᵥ (ofLp x - c))) / |B.det|)) := by
    unfold stdGaussPdf; fun_prop
  have hd : 0 < |B.det| := abs_pos.2 hB
  -- Lebesgue measure is `|det B|` times its image under `T`
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ENNReal.ofReal |B.det| • Measure.map T volume := by
    rw [aux_map_affine c B hB, smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
      mul_inv_cancel₀ hB, abs_one, ENNReal.ofReal_one, one_smul]
  rw [gZonotopeLaw, stdGaussian_eq_withDensity]
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs]
  conv_rhs => rw [hvol]
  rw [Measure.restrict_smul, lintegral_smul_measure, setLIntegral_map hs hψ hT]
  have hinv : ∀ β : EuclideanSpace ℝ (Fin n), toLp 2 (B⁻¹ *ᵥ (ofLp (T β) - c)) = β := by
    intro β
    simp only [T, add_sub_cancel_left]
    rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hB), one_mulVec]
  simp_rw [hinv]
  -- the constant `|det B|⁻¹` cancels the Jacobian
  have hsplit : ∀ β, ENNReal.ofReal (stdGaussPdf n β / |B.det|)
      = ENNReal.ofReal (stdGaussPdf n β) * ENNReal.ofReal |B.det|⁻¹ := by
    intro β
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by unfold stdGaussPdf; positivity)]
  simp_rw [hsplit]
  rw [lintegral_mul_const _ hφ, smul_eq_mul, mul_comm, mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hd.le), inv_mul_cancel₀ hd.ne', ENNReal.ofReal_one, mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
