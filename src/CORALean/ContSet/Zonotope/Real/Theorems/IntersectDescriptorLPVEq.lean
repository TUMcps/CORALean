module

public import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptorLPV
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The polytopic intersection zonotope is the intersection zonotope at the scheduled matrices

[1, Cor. 1]: if the correction matrix is polytopic, `Λ(θ) = Σᵢ ρᵢ(θ) Λᵢ` (its Eq. 14), then the
intersection zonotope [1, Thm. 1] at `A(θ) = Σⱼ ρⱼ Aⱼ`, `B(θ)`, `D(θ)` alike (its Eq. 16) is
`intersectDescriptorLPV`, its Eq. 15: an equality of zonotopes, center and generators. The double
sums come from expanding `(I - Λ(θ)C) T A(θ)` bilinearly, and `I = Σᵢ ρᵢ I` needs `Σᵢ ρᵢ = 1`
[1, Eq. 2]; the weights need not be nonnegative here.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `ρ` – vertex weights
* `Λ` – correction matrices
* `A` – vertex state matrices
* `B` – vertex input matrices
* `D` – vertex disturbance matrices
* `C` – output matrix
* `F` – noise matrix
* `Hd` – disturbance generator matrix
* `u` – control input
* `y` – measurement
* `X` – state zonotope

## Hypotheses
* `hρ` – weights sum to one

## Conclusion
* the LPV zonotope equals the weighted-average descriptor zonotope

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu ny nd m r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- `I - Λ(θ)C = Σᵢ ρᵢ (I - ΛᵢC)` at `Σᵢ ρᵢ = 1`
theorem Zonotope.aux_one_sub_sum (ρ : Fin r → ℝ) (Λ : Fin r → Mat ℝ n ny) (C : Mat ℝ ny n)
    (hρ : ∑ i, ρ i = 1) :
    ∑ i, ρ i • (1 - Λ i * C) = 1 - (∑ i, ρ i • Λ i) * C := by
  simp only [smul_sub, Finset.sum_sub_distrib, Matrix.sum_mul, Matrix.smul_mul]
  rw [← Finset.sum_smul, hρ, one_smul]

-- `(I - Λ(θ)C) T M(θ)` expanded over the vertices
theorem Zonotope.aux_double_sum {k : ℕ} (T : Mat ℝ n n) (ρ : Fin r → ℝ) (Λ : Fin r → Mat ℝ n ny)
    (C : Mat ℝ ny n) (M : Fin r → Mat ℝ n k) (hρ : ∑ i, ρ i = 1) : -- --- CONCL ---
    ∑ i, ∑ j, (ρ i * ρ j) • ((1 - Λ i * C) * T * M j) =
      (1 - (∑ i, ρ i • Λ i) * C) * T * (∑ j, ρ j • M j) := by -- --- PROOF ---
  rw [← Zonotope.aux_one_sub_sum ρ Λ C hρ, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, mul_comm (ρ j)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectDescriptorLPV_eq (T : Mat ℝ n n) (N : Mat ℝ n ny) (ρ : Fin r → ℝ)
    (Λ : Fin r → Mat ℝ n ny) (A : Fin r → Mat ℝ n n) (B : Fin r → Mat ℝ n nu)
    (D : Fin r → Mat ℝ n nd) (C : Mat ℝ ny n) (F : Mat ℝ ny nd) (Hd : Mat ℝ nd m)
    (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) (hρ : ∑ i, ρ i = 1) : -- --- CONCL ---
    X.intersectDescriptorLPV T N ρ Λ A B D C F Hd u y =
      X.intersectDescriptor T N (∑ i, ρ i • Λ i) (∑ j, ρ j • A j) (∑ j, ρ j • B j)
        ((∑ j, ρ j • D j) * Hd) C (F * Hd) u y := by -- --- PROOF ---
  have hone : ∀ {a b : ℕ} (M : Mat ℝ a b), ∑ i, ρ i • M = M := fun M => by
    rw [← Finset.sum_smul, hρ, one_smul]
  have hK := Zonotope.aux_one_sub_sum ρ Λ C hρ
  have hdA := Zonotope.aux_double_sum T ρ Λ C A hρ
  have hdB := Zonotope.aux_double_sum T ρ Λ C B hρ
  have hdD := Zonotope.aux_double_sum T ρ Λ C D hρ
  -- the single sums, affine in `Λᵢ`, at `Σᵢ ρᵢ = 1`
  have hsN : ∑ i, ρ i • ((1 - Λ i * C) * N * F * Hd) =
      (1 - (∑ i, ρ i • Λ i) * C) * N * (F * Hd) := by
    calc ∑ i, ρ i • ((1 - Λ i * C) * N * F * Hd)
        = ∑ i, (ρ i • (1 - Λ i * C)) * (N * (F * Hd)) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (∑ i, ρ i • (1 - Λ i * C)) * (N * (F * Hd)) := (Matrix.sum_mul _ _ _).symm
      _ = _ := by rw [hK, Matrix.mul_assoc]
  have hsF : ∑ i, ρ i • (Λ i * F * Hd) = (∑ i, ρ i • Λ i) * (F * Hd) := by
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have hsD : ∑ i, ∑ j, (ρ i * ρ j) • ((1 - Λ i * C) * T * D j * Hd) =
      (1 - (∑ i, ρ i • Λ i) * C) * T * ((∑ j, ρ j • D j) * Hd) := by
    rw [← Matrix.mul_assoc, ← hdD]
    simp only [Matrix.sum_mul, Matrix.smul_mul]
  have hsy : ∑ i, ρ i • ((N - Λ i * C * N + Λ i) *ᵥ y) =
      (N + ∑ i, ρ i • Λ i - (∑ i, ρ i • Λ i) * C * N) *ᵥ y := by
    simp only [← smul_mulVec, ← sum_mulVec, smul_add, smul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hone, Matrix.sum_mul, Matrix.smul_mul]
    congr 1
    abel
  -- a double sum of vectors is the double sum of matrices applied
  have hv : ∀ {k : ℕ} (M : Fin r → Mat ℝ n k) (v : Vec ℝ k),
      ∑ i, ∑ j, (ρ i * ρ j) • ((1 - Λ i * C) *ᵥ (T *ᵥ (M j *ᵥ v))) =
        (∑ i, ∑ j, (ρ i * ρ j) • ((1 - Λ i * C) * T * M j)) *ᵥ v := fun M v => by
    simp only [sum_mulVec, smul_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp only [Zonotope.intersectDescriptorLPV, Zonotope.intersectDescriptor]
  congr 1
  · -- the center, Eq. 15a
    rw [hsy]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hv A X.c, hv B u, hdA, hdB]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  · -- the generators, Eq. 15b, block by block
    congr 1; congr 1; congr 1
    · funext g; rw [hv A (X.G g), hdA]; simp only [mulVec_mulVec, Matrix.mul_assoc]
    · rw [hsD]
    · rw [hsN]
    · rw [hsF]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
