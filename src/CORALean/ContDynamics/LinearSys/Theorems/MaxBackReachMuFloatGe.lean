module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachMu
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachMuFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope

@[expose] public section

/-!
# The float `μ` is an upper bound of the exact one

`μ`, [1, Alg. 3] line 3, is the radius of the ball `B_μ` that lines 4 and 5 subtract, so an upper
bound keeps the polytope inside the exact one: this is the direction an inner approximation needs.
The float value is the Frobenius bound `√γ ‖M G‖_F` of an entrywise magnitude bound of `M G`, `M =
e^{AΔt} - I` known to lie in `[e^{AΔt}] - I`, and the spectral norm of a matrix is at most its
Frobenius norm — Cauchy-Schwarz row by row. Stated against the exact layer's `μ` of the zonotope
the float one stores.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A norm is nonnegative. -/
theorem aux_l2_opNorm_nonneg {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℝ) :
    0 ≤ (Matrix.instL2OpNormedAddCommGroup (𝕜 := ℝ)).toNorm.norm A := by
  letI := Matrix.instL2OpNormedAddCommGroup (𝕜 := ℝ) (m := Fin m) (n := Fin h)
  exact norm_nonneg A

/-- The spectral norm is at most the root of the sum of the squared entries: the operator norm
of the Euclidean map is bounded by Cauchy-Schwarz on each output coordinate. -/
theorem aux_l2_opNorm_le {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ∑ i, ∑ j, A i j ^ 2 ≤ s ^ 2) :
    (Matrix.instL2OpNormedAddCommGroup (𝕜 := ℝ)).toNorm.norm A ≤ s := by -- --- PROOF ---
  -- the norm is the operator norm of the Euclidean map, so bound it on each vector
  have hdef : (Matrix.instL2OpNormedAddCommGroup (𝕜 := ℝ)).toNorm.norm A
      = ‖((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin h)).trans
          LinearMap.toContinuousLinearMap) A‖ := rfl
  rw [hdef]
  refine ContinuousLinearMap.opNorm_le_bound _ hs0 fun x => ?_
  have h1 : ‖(((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin h)).trans
          LinearMap.toContinuousLinearMap) A) x‖
      = Real.sqrt (∑ i, (∑ j, A i j * x j) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  -- Cauchy-Schwarz on each output coordinate
  have h2 : ‖x‖ = Real.sqrt (∑ j, x j ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp
  rw [h1, h2]
  have hcs : ∀ i, (∑ j, A i j * x j) ^ 2 ≤ (∑ j, A i j ^ 2) * ∑ j, x j ^ 2 :=
    fun i => by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x j)
      simpa using this
  calc Real.sqrt (∑ i, (∑ j, A i j * x j) ^ 2)
      ≤ Real.sqrt ((∑ i, ∑ j, A i j ^ 2) * ∑ j, x j ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun i _ => hcs i
    _ ≤ Real.sqrt (s ^ 2 * ∑ j, x j ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hs
          (Finset.sum_nonneg fun j _ => sq_nonneg _))
    _ = s * Real.sqrt (∑ j, x j ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.maxBackReachMu_le_muFloat (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hη : sys.OrderAdmissibleFloat Δt Δt η) (p : ℕ) (B : Zonotope (Vec 𝕋 n)) :
    sys.maxBackReachMu (toReal Δt) (InflatedContSet.nominal B)
      ≤ toReal (sys.maxBackReachMuFloat Δt η p B) := by -- --- PROOF ---
  set EI := Interval.matPlus (sys.expIntervalFloat Δt Δt η)
    (Interval.point (negIdentityMat 𝕋 n)) with hEI
  -- `e^{AΔt} - I` lies in `[e^{AΔt}] - I`
  have hneg : (-1 : Mat ℝ n n) ∈ (Interval.point (negIdentityMat 𝕋 n)).construct := by
    have h := Interval.mem_point (α := Mat 𝕋 n n) (negIdentityMat 𝕋 n)
    have he : (RealImage.realImage (α := Mat 𝕋 n n) (negIdentityMat 𝕋 n) : Mat ℝ n n) = -1 := by
      funext i j
      show toReal (if i = j then FloatOps.neg (FloatOps.one : 𝕋) else FloatOps.zero)
        = (-1 : Mat ℝ n n) i j
      by_cases hij : i = j
      · rw [if_pos hij, toReal_neg, toReal_one, hij]; simp
      · rw [if_neg hij, toReal_zero]; simp [Matrix.one_apply_ne hij]
    rwa [he] at h
  have hM : exp (toReal Δt • Scalar.toRealMat sys.A) - 1 ∈ EI.construct := by
    have := Interval.matPlus_outer _ _ (sys.exp_mem_expIntervalFloat hη le_rfl le_rfl) hneg
    rwa [← sub_eq_add_neg] at this
  -- the entrywise magnitude bounds, of `e^{AΔt} - I`, of `G`, and of their product
  set M : Mat ℝ n n := exp (toReal Δt • Scalar.toRealMat sys.A) - 1 with hMdef
  set mag : Mat 𝕋 n n := fun i k =>
    maximum (absolute (EI.inf i k)) (absolute (EI.sup i k)) with hmag
  have hMmag : ∀ i k, |M i k| ≤ toReal (mag i k) := fun i k => by
    have hik := hM (i, k)
    simp only [Entrywise.entry_mat] at hik
    rw [hmag]
    show |M i k| ≤ toReal (maximum (absolute (EI.inf i k)) (absolute (EI.sup i k)))
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hik.1 hik.2
  -- the generator matrix `G` of the stored zonotope, entrywise
  set G : Matrix (Fin n) (Fin B.h) ℝ := Matrix.of fun i j => toReal (B.G j i) with hG
  set m : Mat 𝕋 n B.h := fun i j => sumUp fun k => mulUp (mag i k) (absolute (B.G j k)) with hm
  have hMG : ∀ i j, |(M * G) i j| ≤ toReal (m i j) := fun i j => by
    rw [Matrix.mul_apply]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]
    refine le_trans (mul_le_mul (hMmag i k) (le_of_eq ?_) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hMmag i k))) (mul_le_mulUp _ _)
    rw [toReal_absolute]; rfl
  -- the Frobenius bound, then the root of it, squared, above the sum of squares
  set frobSq := sumUp fun i => sqSumUp (m i) with hfrob
  have hF : ∑ i, ∑ j, (M * G) i j ^ 2 ≤ toReal frobSq := by
    refine le_trans (Finset.sum_le_sum fun i _ => sq_sum_le_sqSumUp (fun j => hMG i j)) ?_
    exact sum_le_sumUp _
  have hs2 : ∑ i, ∑ j, (M * G) i j ^ 2 ≤ toReal (sqrtUp p frobSq) ^ 2 := by
    refine le_trans hF ?_
    have h0 := le_sqrtUp p frobSq
    have hnn : 0 ≤ toReal frobSq := by
      refine le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) hF
    calc toReal frobSq = Real.sqrt (toReal frobSq) ^ 2 := (Real.sq_sqrt hnn).symm
      _ ≤ toReal (sqrtUp p frobSq) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h0 2
  have hnorm := aux_l2_opNorm_le (M * G) (sqrtUp_nonneg p frobSq) hs2
  -- `√γ`, from `γ` counted up
  have hγ : Real.sqrt (B.h : ℝ) ≤ toReal (sqrtUp p (nsmulUp B.h (FloatOps.one : 𝕋))) := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_sqrtUp p (nsmulUp B.h (FloatOps.one : 𝕋)))
    have := le_nsmulUp B.h (FloatOps.one : 𝕋)
    rwa [toReal_one, mul_one] at this
  unfold LinearSys.maxBackReachMu LinearSys.maxBackReachMuFloat
  refine le_trans ?_ (mul_le_mulUp _ _)
  refine mul_le_mul ?_ ?_ ?_ (le_trans (Real.sqrt_nonneg _) hγ)
  · exact hγ
  · exact hnorm
  · exact aux_l2_opNorm_nonneg _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
