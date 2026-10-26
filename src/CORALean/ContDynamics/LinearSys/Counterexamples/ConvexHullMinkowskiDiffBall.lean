module

public import CORALean.ContSet.ContSet.Interfaces
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCritical
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import CORALean.Global.EuclideanGenOpNorm
public import CORALean.Specification.STL.Operations.DepCurvatureF
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The inner time-interval set of TAC 2026, (21), is not inner

[1, Eq. (21)] claims `H(τ_k) ⊇ (conv(H(t_k), H(t_{k+1})) ⊖ F H(t_k)) ⊖ B_µ` for the flow (17),
`µ = √γ‖(e^{AΔt} - I)G‖₂` (22), citing [2, Prop. 1]. Refuted for `ẋ = (x₂, x₃, 0)`, `Δt = 1/8`,
`η ≥ 2` and the box `H(0) = ⟨(0, 0, 256), diag(1, 1/4, 1/4)⟩`: `A³ = 0`, so `E = 0` (20), `F` (19)
is `[-1/512, 0]` at `(1, 3)` only, `F H(0) ⊆ [-1025/2048, 0] × 0 × 0`, and `µ ≤ 1/9`. The point
`(7/4, 16, 256)`, the midpoint of `x₀ = (3/4, 0, 256)` and `e^{AΔt}x₀`, is in the set, and in the
erode-first hull `conv(H(t_k) ⊖ F H(t_k) ⊖ B_µ, H(t_{k+1}) ⊖ F H(t_k) ⊖ B_µ)`; no run reaches it,
as its start would have first coordinate `5/4 + 128(t - 1/16)² > 1`. The chord of `x₀` bulges
away from its trajectory, and `⊖ F H` trims the hull on the trajectory's side, not the chord's.

## Inputs
* `η` – Taylor order

## Hypotheses
* `hη` – Taylor order at least two

## Conclusion
* a point of (21)'s set, and of its erode-first form, is on no trajectory over `[0, Δt]`

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
* [2] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The chain `A = [0 1 0; 0 0 1; 0 0 0]` is nilpotent: `Aⁱ = 0` for `i ≥ 3`. -/
private theorem LinearSys.aux_chain_pow_eq_zero {i : ℕ} (hi : 3 ≤ i) :
    (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) ^ i = 0 :=
  pow_eq_zero_of_le hi (by
    ext j k; fin_cases j <;> fin_cases k <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three])

/-- The chain's exponential stops after its quadratic term: `e^{tA} = I + tA + (t²/2)A²`. -/
private theorem LinearSys.aux_exp_smul_chain (t : ℝ) : -- --- CONCL ---
    exp (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) =
      1 + t • !![0, 1, 0; 0, 0, 1; 0, 0, 0] +
        (t ^ 2 / 2) • !![0, 1, 0; 0, 0, 1; 0, 0, 0] ^ 2 := by -- --- PROOF ---
  rw [exp_eq_tsum ℝ]
  show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) • (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) ^ i = _
  rw [tsum_eq_sum (s := Finset.range 3) fun b hb => by
    rw [smul_pow, LinearSys.aux_chain_pow_eq_zero (by simp at hb; omega), smul_zero, smul_zero]]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, smul_pow]
  simp [Nat.factorial, smul_smul, div_eq_inv_mul, add_assoc]

/-- The chain's flow, coordinatewise: `e^{tA}x = (x₁ + t x₂ + (t²/2) x₃, x₂ + t x₃, x₃)`. -/
private theorem LinearSys.aux_exp_smul_chain_mulVec (t : ℝ) (x : Vec ℝ 3) :
    exp (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) *ᵥ x =
      ![x 0 + t * x 1 + t ^ 2 / 2 * x 2, x 1 + t * x 2, x 2] := by
  rw [LinearSys.aux_exp_smul_chain]
  ext i; fin_cases i <;>
    simp [sq, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `E(Δt, η) = 0` (20) for the chain and `η ≥ 2`: `|A| = A`, and `e^{AΔt}` is its own quadratic
Taylor polynomial. -/
private theorem LinearSys.aux_expRemainderMat_chain (Δt : ℝ) {η : ℕ} (hη : 2 ≤ η) : -- --- CONCL ---
    Real.MatExp.expRemainderMat (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) Δt η =
      0 := by -- --- PROOF ---
  -- `|A| = A`
  have habs : Real.MatExp.absMat (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) =
      !![0, 1, 0; 0, 0, 1; 0, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Real.MatExp.absMat]
  -- both are the first three terms of the series
  have hz : ∀ i ∉ Finset.range 3, ((i.factorial : ℝ)⁻¹) •
      (Δt • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) ^ i = 0 := fun i hi => by
    rw [smul_pow, LinearSys.aux_chain_pow_eq_zero (by simp at hi; omega), smul_zero, smul_zero]
  have hexp : exp (Δt • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) = ∑ i ∈ Finset.range 3,
      ((i.factorial : ℝ)⁻¹) • (Δt • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) ^ i := by
    rw [exp_eq_tsum ℝ]
    exact tsum_eq_sum hz
  have htay : Real.MatExp.expTaylor (Δt • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) η =
      ∑ i ∈ Finset.range 3,
        ((i.factorial : ℝ)⁻¹) • (Δt • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) ^ i := by
    rw [Real.MatExp.expTaylor]
    exact (Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      fun i _ hi => hz i hi).symm
  rw [Real.MatExp.expRemainderMat, habs, hexp, htay, sub_self]

/-- The `i = 2` term of `F` (19) for the chain is `-Δt²/8` times `A²`, and every later one is
zero. -/
private theorem LinearSys.aux_corrTerm_chain (Δt : ℝ) (i : ℕ) (j k : Fin 3) : -- --- CONCL ---
    Real.MatExp.corrTerm (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) Δt (i + 2) j k =
      if i = 0 then -(Δt ^ 2 / 8) * (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k
      else 0 := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · -- `i^{-i/(i-1)} - i^{-1/(i-1)} = -1/4` at `i = 2`, and `A²` has its one at `(1, 3)`
    have hcrit : Real.MatExp.corrCoeff 2 = -1 / 4 := by
      simp only [Real.MatExp.corrCoeff, Real.MatExp.corrCritical]
      norm_num [Real.rpow_neg_one]
    have hA2 : (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
      ext j k; fin_cases j <;> fin_cases k <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Real.MatExp.corrTerm, hcrit, zero_add, hA2, if_true, Nat.factorial_two]
    push_cast
    ring
  · -- `Aⁱ⁺² = 0` past `i = 0`
    rw [if_neg (by omega)]
    simp [Real.MatExp.corrTerm, LinearSys.aux_chain_pow_eq_zero (i := i + 2) (by omega)]

/-- A matrix of the chain's `F` (19), `η ≥ 2`, maps `x` to `(N₁₃ x₃, 0, 0)`, with `N₁₃` in
`[-Δt²/8, 0]`. -/
private theorem LinearSys.aux_mulVec_of_mem_depCurvatureF_chain (Δt : ℝ) {η : ℕ} (hη : 2 ≤ η)
    (N : Mat ℝ 3 3) (hN : N ∈ (STL.depCurvatureF !![0, 1, 0; 0, 0, 1; 0, 0, 0] Δt η).construct)
    (x : Vec ℝ 3) : -- --- CONCL ---
    N *ᵥ x = ![N 0 2 * x 2, 0, 0] ∧ -(Δt ^ 2 / 8) ≤ N 0 2 ∧ N 0 2 ≤ 0 := by -- --- PROOF ---
  -- the sums over `i` keep their `i = 0` term only
  have hsum : ∀ (g : ℝ → ℝ) (j k : Fin 3), g 0 = 0 →
      ∑ i ∈ Finset.range (η - 1),
        g (Real.MatExp.corrTerm (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) Δt (i + 2) j k) =
        g (-(Δt ^ 2 / 8) * (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k) := by
    intro g j k hg
    obtain ⟨m, hm⟩ : ∃ m, η - 1 = m + 1 := ⟨η - 2, by omega⟩
    rw [hm, Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by
      rw [LinearSys.aux_corrTerm_chain, if_neg (by omega), hg]]
    rw [LinearSys.aux_corrTerm_chain, if_pos rfl, zero_add]
  -- each entry lies between `-Δt²/8 (A²)ⱼₖ` and `0`, as `E = 0`
  have hb : ∀ j k,
      min (-(Δt ^ 2 / 8) * (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k) 0 ≤ N j k ∧
      N j k ≤ max (-(Δt ^ 2 / 8) * (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k) 0 :=
    fun j k => by
      have := hN (j, k)
      simp only [STL.depCurvatureF, Entrywise.entry_mat,
        LinearSys.aux_expRemainderMat_chain Δt hη, Matrix.zero_apply, sub_zero, add_zero] at this
      rwa [hsum (fun r => min r 0) j k (by simp), hsum (fun r => max r 0) j k (by simp)] at this
  -- so the entries off `(1, 3)` are zero
  have hzero : ∀ j k, (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k = 0 → N j k = 0 :=
    fun j k h => by
      have := hb j k
      rw [h, mul_zero, min_self, max_self] at this
      exact le_antisymm this.2 this.1
  have h02 := hb 0 2
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    mul_one] at h02
  have hd : -(Δt ^ 2 / 8) ≤ 0 := by nlinarith [sq_nonneg Δt]
  rw [min_eq_left hd, max_eq_right hd] at h02
  refine ⟨?_, h02⟩
  -- the product keeps the `(1, 3)` entry times `x₃`
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hzero 0 0 (by simp),
      hzero 0 1 (by simp),
      hzero 1 0 (by simp), hzero 1 1 (by simp), hzero 1 2 (by simp), hzero 2 0 (by simp),
      hzero 2 1 (by simp), hzero 2 2 (by simp)]

/-- The box `⟨(0, 0, 256), diag(1, 1/4, 1/4)⟩`, coordinatewise. -/
private theorem LinearSys.aux_mem_chainBox (x : Vec ℝ 3) : -- --- CONCL ---
    x ∈ (⟨3, ![0, 0, 256], ![![1, 0, 0], ![0, 1 / 4, 0], ![0, 0, 1 / 4]]⟩ :
      Real.Zonotope (Vec ℝ 3)).construct ↔
      |x 0| ≤ 1 ∧ |x 1| ≤ 1 / 4 ∧ |x 2 - 256| ≤ 1 / 4 := by -- --- PROOF ---
  constructor
  · rintro ⟨β, hβ, rfl⟩
    simp [Fin.sum_univ_three, abs_mul]
    exact ⟨hβ 0, hβ 1, hβ 2⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨![x 0, 4 * x 1, 4 * (x 2 - 256)], fun j => ?_, ?_⟩
    · fin_cases j <;> simp [abs_mul] <;> linarith
    · ext i; fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-- `µ` (22) for the chain's box and `Δt = 1/8` is at most `1/9`: the images of the generators
have lengths `0`, `1/32` and at most `157/5000`. -/
private theorem LinearSys.aux_mu_chainBox_le : -- --- CONCL ---
    Real.sqrt 3 * genOpNorm₂ (fun j => (exp ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] :
      Mat ℝ 3 3)) - 1) *ᵥ (![![1, 0, 0], ![0, 1 / 4, 0], ![0, 0, 1 / 4]] : Fin 3 → Vec ℝ 3) j) ≤
      1 / 9 := by -- --- PROOF ---
  set g := genOpNorm₂ (fun j => (exp ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] :
      Mat ℝ 3 3)) - 1) *ᵥ (![![1, 0, 0], ![0, 1 / 4, 0], ![0, 0, 1 / 4]] : Fin 3 → Vec ℝ 3) j)
  -- the images `0`, `(1/32, 0, 0)` and `(1/512, 1/32, 0)`, their lengths summed
  have hg : g ≤ 1 / 32 + 157 / 5000 := by
    refine (genOpNorm₂_le_sum_norm₂ _).trans ?_
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, LinearSys.aux_exp_smul_chain_mulVec,
      Fin.sum_univ_three, norm₂]
    simp
    have e2 : Real.sqrt ((2⁻¹ * (8 ^ 2)⁻¹ * 4⁻¹) ^ 2 + (8⁻¹ * 4⁻¹) ^ 2) ≤ 157 / 5000 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    norm_num at e2 ⊢
    linarith
  have hg0 : 0 ≤ g := genOpNorm₂_nonneg _
  -- `3 (1/32 + 157/5000)² ≤ 1/81`
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg 3
  nlinarith [mul_nonneg hs0 hg0, mul_le_mul_of_nonneg_left hg hs0]

/-- (21)'s set holds `(7/4, 16, 256)`: shifted by `y ∈ B_µ` and `z ∈ F H(0)`, it is the midpoint of
the chord of a point of the box `S` under the step `M = e^{AΔt}`. -/
private theorem LinearSys.aux_mem_convexHull_chainBox (S : Set (Vec ℝ 3))
    (hS : ∀ x, x ∈ S ↔ |x 0| ≤ 1 ∧ |x 1| ≤ 1 / 4 ∧ |x 2 - 256| ≤ 1 / 4) (M : Mat ℝ 3 3)
    (hM : ∀ x, M *ᵥ x = ![x 0 + x 1 / 8 + x 2 / 128, x 1 + x 2 / 8, x 2]) (y z : Vec ℝ 3)
    (hy : ∀ i, |y i| ≤ 1 / 9) (hz0 : -1025 / 2048 ≤ z 0) (hz0' : z 0 ≤ 0) (hz1 : z 1 = 0)
    (hz2 : z 2 = 0) : -- --- CONCL ---
    ![7 / 4, 16, 256] + y + z ∈ convexHull ℝ (S ∪ (M *ᵥ ·) '' S) := by -- --- PROOF ---
  have hy0 := abs_le.mp (hy 0)
  have hy1 := abs_le.mp (hy 1)
  have hy2 := abs_le.mp (hy 2)
  -- the chord's starting point
  have hx : (![3 / 4 + y 0 + z 0 - y 1 / 16, y 1 - y 2 / 16, 256 + y 2] : Vec ℝ 3) ∈ S :=
    (hS _).mpr ⟨show |3 / 4 + y 0 + z 0 - y 1 / 16| ≤ 1 from
        abs_le.mpr ⟨by linarith, by linarith⟩,
      show |y 1 - y 2 / 16| ≤ 1 / 4 from abs_le.mpr ⟨by linarith, by linarith⟩,
      show |256 + y 2 - 256| ≤ 1 / 4 from abs_le.mpr ⟨by linarith, by linarith⟩⟩
  -- the point is its chord's midpoint
  apply segment_subset_convexHull (mem_union_left _ hx)
    (mem_union_right S (mem_image_of_mem _ hx))
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [hM]
  ext i
  fin_cases i
  · show 1 / 2 * (3 / 4 + y 0 + z 0 - y 1 / 16) + 1 / 2 * ((3 / 4 + y 0 + z 0 - y 1 / 16) +
      (y 1 - y 2 / 16) / 8 + (256 + y 2) / 128) = 7 / 4 + y 0 + z 0
    ring
  · show 1 / 2 * (y 1 - y 2 / 16) + 1 / 2 * ((y 1 - y 2 / 16) + (256 + y 2) / 8) =
      16 + y 1 + z 1
    rw [hz1]; ring
  · show 1 / 2 * (256 + y 2) + 1 / 2 * (256 + y 2) = 256 + y 2 + z 2
    rw [hz2]; ring

/-- The erode-first set holds `(7/4, 16, 256)` too: `x₀ = (3/4, 0, 256)` and `Mx₀`, `M = e^{AΔt}`,
stay in the box `S` and its image when shifted by `y ∈ B_µ` and `z ∈ F H(0)`. -/
private theorem LinearSys.aux_add_mem_chainBox (S : Set (Vec ℝ 3))
    (hS : ∀ x, x ∈ S ↔ |x 0| ≤ 1 ∧ |x 1| ≤ 1 / 4 ∧ |x 2 - 256| ≤ 1 / 4) (M : Mat ℝ 3 3)
    (hM : ∀ x, M *ᵥ x = ![x 0 + x 1 / 8 + x 2 / 128, x 1 + x 2 / 8, x 2]) (y z : Vec ℝ 3)
    (hy : ∀ i, |y i| ≤ 1 / 9) (hz0 : -1025 / 2048 ≤ z 0) (hz0' : z 0 ≤ 0) (hz1 : z 1 = 0)
    (hz2 : z 2 = 0) : -- --- CONCL ---
    ![3 / 4, 0, 256] + y + z ∈ S ∧
      M *ᵥ ![3 / 4, 0, 256] + y + z ∈ (M *ᵥ ·) '' S := by -- --- PROOF ---
  have hy0 := abs_le.mp (hy 0)
  have hy1 := abs_le.mp (hy 1)
  have hy2 := abs_le.mp (hy 2)
  -- `x₀` shifted stays in the box
  refine ⟨(hS _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · show |3 / 4 + y 0 + z 0| ≤ 1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · show |0 + y 1 + z 1| ≤ 1 / 4
    rw [hz1]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · show |256 + y 2 + z 2 - 256| ≤ 1 / 4
    rw [hz2]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the preimage `x₀ + e^{-AΔt}(y + z)`
  refine ⟨![3 / 4 + (y 0 + z 0) - y 1 / 8 + y 2 / 128, y 1 - y 2 / 8, 256 + y 2],
    (hS _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · show |3 / 4 + (y 0 + z 0) - y 1 / 8 + y 2 / 128| ≤ 1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · show |y 1 - y 2 / 8| ≤ 1 / 4
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · show |256 + y 2 - 256| ≤ 1 / 4
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- and is mapped onto `e^{AΔt}x₀ + y + z`
  beta_reduce
  rw [hM, hM]
  ext i
  fin_cases i
  · show 3 / 4 + (y 0 + z 0) - y 1 / 8 + y 2 / 128 + (y 1 - y 2 / 8) / 8 +
      (256 + y 2) / 128 = 3 / 4 + 0 / 8 + 256 / 128 + y 0 + z 0
    ring
  · show y 1 - y 2 / 8 + (256 + y 2) / 8 = 0 + 256 / 8 + y 1 + z 1
    rw [hz1]; ring
  · show 256 + y 2 = 256 + y 2 + z 2
    rw [hz2]; ring

/-- No run of the chain from the box `S` passes `(7/4, 16, 256)`: its start would have first
coordinate `5/4 + 128(t - 1/16)²`. -/
private theorem LinearSys.aux_ne_of_mem_chainBox (S : Set (Vec ℝ 3))
    (hS : ∀ x, x ∈ S ↔ |x 0| ≤ 1 ∧ |x 1| ≤ 1 / 4 ∧ |x 2 - 256| ≤ 1 / 4) (t : ℝ) (x : Vec ℝ 3)
    (hx : x ∈ S) : -- --- CONCL ---
    exp (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) *ᵥ x ≠
      ![7 / 4, 16, 256] := by -- --- PROOF ---
  intro h
  rw [LinearSys.aux_exp_smul_chain_mulVec] at h
  have e0 : x 0 + t * x 1 + t ^ 2 / 2 * x 2 = 7 / 4 := congrFun h 0
  have e1 : x 1 + t * x 2 = 16 := congrFun h 1
  have e2 : x 2 = 256 := congrFun h 2
  have h0 := (abs_le.mp ((hS x).mp hx).1).2
  rw [e2] at e0 e1
  nlinarith [sq_nonneg (t - 1 / 16)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.convexHull_minkowskiDiff_ball_counterexample (η : ℕ)
    (hη : 2 ≤ η) : -- --- CONCL ---
    let A : Mat ℝ 3 3 := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
    let Δt : ℝ := 1 / 8
    let Z : Real.Zonotope (Vec ℝ 3) :=
      ⟨3, ![0, 0, 256], ![![1, 0, 0], ![0, 1 / 4, 0], ![0, 0, 1 / 4]]⟩
    let H₀ := Z.construct -- H(t_k)
    let H₁ := (exp (Δt • A) *ᵥ ·) '' H₀ -- H(t_{k+1})
    let Hτ := ⋃ t ∈ Icc (0 : ℝ) Δt, (exp (t • A) *ᵥ ·) '' H₀ -- H(τ_k)
    let FH := ⋃ N ∈ (STL.depCurvatureF A Δt η).construct, (N *ᵥ ·) '' H₀ -- (19), (20)
    let μ := Real.sqrt (Z.h : ℝ) * genOpNorm₂ fun j => (exp (Δt • A) - 1) *ᵥ Z.G j -- (22)
    let Bμ := {y : Vec ℝ 3 | ‖y‖₂ ≤ μ}
    ![7 / 4, 16, 256] ∈ minkowskiDiff (minkowskiDiff (convexHull ℝ (H₀ ∪ H₁)) FH) Bμ ∧
      ![7 / 4, 16, 256] ∈ convexHull ℝ
        (minkowskiDiff (minkowskiDiff H₀ FH) Bμ ∪ minkowskiDiff (minkowskiDiff H₁ FH) Bμ) ∧
      ![7 / 4, 16, 256] ∉ Hτ := by -- --- PROOF ---
  intro A Δt Z H₀ H₁ Hτ FH μ Bμ
  have hmem : ∀ x, x ∈ H₀ ↔ |x 0| ≤ 1 ∧ |x 1| ≤ 1 / 4 ∧ |x 2 - 256| ≤ 1 / 4 :=
    LinearSys.aux_mem_chainBox
  -- `e^{AΔt}x = (x₁ + x₂/8 + x₃/128, x₂ + x₃/8, x₃)`
  have hM : ∀ x, exp (Δt • A) *ᵥ x = ![x 0 + x 1 / 8 + x 2 / 128, x 1 + x 2 / 8, x 2] :=
    fun x => by
      rw [LinearSys.aux_exp_smul_chain_mulVec]
      ext i; fin_cases i <;> norm_num [Δt] <;> ring
  -- `F H(0) ⊆ [-1025/2048, 0] × 0 × 0`
  have hFH : ∀ z ∈ FH, -1025 / 2048 ≤ z 0 ∧ z 0 ≤ 0 ∧ z 1 = 0 ∧ z 2 = 0 := by
    intro z hz
    simp only [FH, mem_iUnion, mem_image] at hz
    obtain ⟨N, hN, x, hx, rfl⟩ := hz
    obtain ⟨hNx, hlo, hhi⟩ := LinearSys.aux_mulVec_of_mem_depCurvatureF_chain Δt hη N hN x
    have h2 := abs_le.mp ((hmem x).mp hx).2.2
    rw [hNx]
    norm_num [Δt] at hlo
    exact ⟨by show -1025 / 2048 ≤ N 0 2 * x 2; nlinarith,
      by show N 0 2 * x 2 ≤ 0; nlinarith, rfl, rfl⟩
  -- (22): every coordinate of a point of `B_µ` is in `[-1/9, 1/9]`
  have hB : ∀ y ∈ Bμ, ∀ i, |y i| ≤ 1 / 9 := fun y hy i =>
    ((abs_le_norm₂ y i).trans hy).trans (by
      show Real.sqrt ((3 : ℕ) : ℝ) * _ ≤ _
      rw [Nat.cast_ofNat]
      exact LinearSys.aux_mu_chainBox_le)
  refine ⟨fun y hy z hz => ?_, ?_, ?_⟩
  · obtain ⟨h0, h0', h1, h2⟩ := hFH z hz
    exact LinearSys.aux_mem_convexHull_chainBox H₀ hmem _ hM y z (hB y hy) h0 h0' h1 h2
  · -- erode first: the midpoint of `x₀ = (3/4, 0, 256)` and `e^{AΔt}x₀`
    have hx₀ : (![3 / 4, 0, 256] : Vec ℝ 3) ∈ minkowskiDiff (minkowskiDiff H₀ FH) Bμ := by
      intro y hy z hz
      obtain ⟨h0, h0', h1, h2⟩ := hFH z hz
      exact (LinearSys.aux_add_mem_chainBox H₀ hmem _ hM y z (hB y hy) h0 h0' h1 h2).1
    have hx₁ : exp (Δt • A) *ᵥ ![3 / 4, 0, 256] ∈ minkowskiDiff (minkowskiDiff H₁ FH) Bμ := by
      intro y hy z hz
      obtain ⟨h0, h0', h1, h2⟩ := hFH z hz
      exact (LinearSys.aux_add_mem_chainBox H₀ hmem _ hM y z (hB y hy) h0 h0' h1 h2).2
    apply segment_subset_convexHull (mem_union_left _ hx₀) (mem_union_right _ hx₁)
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [LinearSys.aux_exp_smul_chain_mulVec]
    ext i; fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · -- no run over `[0, 1/8]` passes the point
    simp only [Hτ, mem_iUnion, mem_image, not_exists, not_and]
    exact fun t _ x hx => LinearSys.aux_ne_of_mem_chainBox H₀ hmem t x hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
