import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq
import CORALean.ContDynamics.LinearSys.Theorems.NormLeOfMemInputReach
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpMulVecSubInterpolateLe
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.Cube
import CORALean.ContSet.Zonotope.Real.Theorems.CubeExact
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# The first time interval, enclosed by a zonotope

[1, Lemma 2], first half: `R_[0,r](Z) ⊆ P + □(α_r + β_r)`, with `P` the zonotope of
eq. 5 of [1], `(c + e^{rA}c)/2` and generators `(gᵢ ± e^{rA}gᵢ)/2`, `(c - e^{rA}c)/2` — which is
`Zonotope.linComb Z (e^{rA}Z)`, CORA's `enclose` — and `α_r = (e^{r‖A‖} - 1 - r‖A‖) sup ‖x‖`.

`R_[0,r](Z)` is the union of `Φ_t(Z)` over `t ∈ [0, r]`, each `Φ_t(Z)` a
`reachSet` on `[0, t]`, as Sec. 3 of [1] defines it. A point of `Φ_t(Z)` is
`e^{tA}z + v`; `z + (t/r)(e^{rA}z - z)` is on a segment from `Z` to `e^{rA}Z`, so in `P`, and
the rest is at most `α_r` (eq. 6, `MatExp.norm_exp_mulVec_sub_interpolate_le`) plus
`β_t ≤ β_r` (eq. 3 of [1]).

`sup_{x∈Z} ‖x‖` is taken as any bound `s` on `Z`'s norms, the supremum being the least; the
enclosure only grows with `s`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2], conservative approximation: `R_[0,r](Z) ⊆ P + □(α_r + β_r)`. -/
theorem LinearSys.iUnion_reachSet_subset_linComb_plus_cube (sys : LinearSys 𝕋 n)
    (Z U : Zonotope (Vec ℝ n)) {μ r s : ℝ} (hA : 0 < ‖toRealMat sys.A‖) (hr : 0 ≤ r)
    (hμ : 0 ≤ μ) (hU : U.construct = Metric.closedBall 0 μ)
    (hs : ∀ z ∈ Z.construct, ‖z‖ ≤ s) :
    ⋃ t ∈ Set.Icc (0:ℝ) r, sys.reachSet (S := 𝒵) (Set.Icc 0 t) Z U t
      ⊆ ((Z.linComb (Z.mtimes (exp (r • toRealMat sys.A)))).plus
          (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖) * s
            + (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖
              * μ))).construct := by -- --- PROOF ---
  set A := toRealMat sys.A
  set a := ‖A‖
  have hx := Real.add_one_le_exp (r * a)
  have hx0 : 0 ≤ r * a := mul_nonneg hr hA.le
  have hα0 : 0 ≤ Real.exp (r * a) - 1 - r * a := by linarith
  have hUle : ∀ u ∈ construct U, ‖u‖ ≤ μ := fun u hu => by
    have : u ∈ Metric.closedBall (0 : Vec ℝ n) μ := hU ▸ hu
    exact mem_closedBall_zero_iff.mp this
  intro y hy
  obtain ⟨t, ⟨ht0, htr⟩, hyt⟩ := Set.mem_iUnion₂.mp hy
  rw [sys.reachSet_eq (S := 𝒵) Z U ht0 (Zonotope.isBounded_construct U)] at hyt
  obtain ⟨_, ⟨z, hz, rfl⟩, v, hv, rfl⟩ := hyt
  have hz0 : 0 ≤ s := (norm_nonneg z).trans (hs z hz)
  have hβ0 : 0 ≤ (Real.exp (r * a) - 1) / a * μ := mul_nonneg (div_nonneg (by linarith) hA.le) hμ
  -- the point of the segment from `z` to `e^{rA}z`, at the fraction `t / r`
  have hlam : t / r ∈ Set.Icc (0:ℝ) 1 := by
    rcases hr.eq_or_lt with h | h
    · rw [← h, div_zero]; exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨div_nonneg ht0 hr, (div_le_one h).mpr htr⟩
  set p : Vec ℝ n := (1 - t / r) • z + (t / r) • (exp (r • A) *ᵥ z) with hp
  have hpP : p ∈ (Z.linComb (Z.mtimes (exp (r • A)))).construct := by
    refine Zonotope.linComb_outer _ _ ⟨z, hz, exp (r • A) *ᵥ z, ?_, 1 - t / r,
      ⟨by linarith [hlam.2], by linarith [hlam.1]⟩, by rw [hp, sub_sub_cancel]⟩
    rw [← Zonotope.mtimes_exact]; exact ⟨z, hz, rfl⟩
  -- what is left over: the interpolation error and the input's reach
  have hint := MatExp.norm_exp_mulVec_sub_interpolate_le A ht0 htr z
  have hinput : ‖v‖ ≤ (Real.exp (r * a) - 1) / a * μ := by
    refine (sys.norm_le_of_mem_inputReach hA ht0 hUle hv).trans ?_
    have : Real.exp (t * a) ≤ Real.exp (r * a) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right htr hA.le)
    gcongr
  have hrest : ‖(exp (t • A)).mulVecLin z + v - p‖
      ≤ (Real.exp (r * a) - 1 - r * a) * s + (Real.exp (r * a) - 1) / a * μ := by
    have heq : (exp (t • A)).mulVecLin z + v - p
        = (exp (t • A) *ᵥ z - z - (t / r) • (exp (r • A) *ᵥ z - z)) + v := by
      rw [hp, Matrix.mulVecLin_apply]; module
    rw [heq]
    refine (norm_add_le _ _).trans (add_le_add (hint.trans ?_) hinput)
    exact mul_le_mul_of_nonneg_left (hs z hz) hα0
  rw [← Zonotope.plus_exact, Zonotope.cube_exact n (add_nonneg (mul_nonneg hα0 hz0) hβ0)]
  exact ⟨p, hpP, _, mem_closedBall_zero_iff.mpr hrest, add_sub_cancel p _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
