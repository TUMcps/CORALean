module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.CutShape
public import CORALean.ContSet.Ellipsoid.Real.Operations.CutPrecision
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The explicit inverse of the cut ellipsoid's shape matrix

`cutShape * cutPrecision = 1` for a unit `c`, `n ≥ 2` and `0 < γ`, `nγ² < 1`: with `P = c cᵀ`,
`P P = P`, so `(I − κP)(I + λP) = I + (λ − κ − κλ) P`, and the coefficient vanishes for
`λ = κ/(1 − κ)`. It is the matrix of [1, Eq. 16] being invertible, with the inverse
that the containment of [1, Lemma 4.3 (containment)] is stated against.

## Inputs
* `c` – unit cut direction
* `γ` – cut depth

## Hypotheses
* `hc` – `c` has unit length
* `hn` – `2 ≤ n`
* `hγ` – `0 < γ`
* `hγn` – `n γ² < 1`

## Conclusion
* the cut shape times `cutPrecision` is the identity

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_P_mul (c : Vec ℝ n) (hc : c ⬝ᵥ c = 1) : -- --- CONCL ---
    (vecMulVec c c : Mat ℝ n n) * vecMulVec c c = vecMulVec c c := by -- --- PROOF ---
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply]
  have : ∑ k, c i * c k * (c k * c j) = c i * (c ⬝ᵥ c) * c j := by
    rw [dotProduct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, hc]; ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 16]'s shape matrix times `cutPrecision` is the identity. -/
theorem Ellipsoid.cutShape_mul_cutPrecision {c : Vec ℝ n} (hc : c ⬝ᵥ c = 1) {γ : ℝ}
    (hn : 2 ≤ n) (hγ : 0 < γ) (hγn : (n : ℝ) * γ ^ 2 < 1) : -- --- CONCL ---
    Ellipsoid.cutShape n c γ * Ellipsoid.cutPrecision n c γ = 1 := by -- --- PROOF ---
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ]
  have h2 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hP := Ellipsoid.aux_P_mul c hc
  unfold Ellipsoid.cutShape Ellipsoid.cutPrecision
  rw [smul_mul_smul_comm]
  set κ := (1 - (n : ℝ) * γ ^ 2) / (1 - γ ^ 2) with hκ
  set l := (1 - (n : ℝ) * γ ^ 2) / (((n : ℝ) - 1) * γ ^ 2) with hl
  -- the product is `1 + (l − κ − κ l) P`
  have hprod : (1 - κ • vecMulVec c c : Mat ℝ n n) * (1 + l • vecMulVec c c)
      = 1 + (l - κ - κ * l) • vecMulVec c c := by
    simp only [mul_add, sub_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, hP]
    module
  have hcoef : l - κ - κ * l = 0 := by
    rw [hκ, hl]; field_simp; ring
  rw [hprod, hcoef, zero_smul, add_zero]
  have : (↑n * (1 - γ ^ 2) / (↑n - 1) * ((↑n - 1) / (↑n * (1 - γ ^ 2))) : ℝ) = 1 := by
    field_simp
  rw [this, one_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
