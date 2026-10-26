module

public import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerGain
public import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerUpdate
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The Luenberger gain minimizes the Frobenius norm

[1, Prop. 2]: for `⟨ĉ, Ĝ⟩`, `Λ = F Ĝ Ĝᵀ Γᵀ (Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ)⁻¹` (Eq. 31) minimizes `‖Ḡ‖_F` of
`Zonotope.luenbergerUpdate` over all gains `Λ'`. The paper sets the gradient of Eq. 32 to zero,
Eq. 34; here the cost at `Λ'` is the cost at `Λ` plus `‖(Λ' - Λ) Γ Ĝ‖²_F + ‖(Λ' - Λ) R‖²_F`, as
the stationarity `(F - Λ Γ) Ĝ Ĝᵀ Γᵀ = Λ R Rᵀ` kills the cross terms. [2, Thm. 5 (F-radius)] is
the same theorem for Combastel's step `R₊ = [(A - G C) R̄, E, -G F]` and gain `G* = A P̄ Cᵀ S⁻¹`,
`S = C P̄ Cᵀ + F Fᵀ`, `P̄ = R̄ R̄ᵀ` (Eqs. 21-22): `A, C, E, F, R̄` are `F, Γ, Q, R, Ĝ` here, and `Ḡ`
lists the blocks of `R₊` in another order. Neither paper assumes `Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ` invertible,
though both write its inverse; `hS` supplies it.

## Inputs
* `F` – dynamics matrix
* `Γ` – stacked measurement matrix
* `Q` – process-noise generators
* `R` – measurement-noise generators
* `y` – stacked output
* `X` – zonotope
* `Λ'` – competing gain

## Hypotheses
* `hS` – innovation covariance invertible

## Conclusion
* the gain minimizes the generator Frobenius norm

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute, 2023.
* [2] C. Combastel. "Zonotopes and Kalman observers: Gain optimality under distinct uncertainty
      paradigms and robust convergence". Automatica, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p nq nr : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sum of products of entries is a trace. -/
private theorem Zonotope.aux_sum_mul_eq_trace {a b : ℕ} (M N : Mat ℝ a b) :
    ∑ i, ∑ j, M i j * N i j = trace (M * Nᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

/-- Eq. 32: the squared Frobenius norm of `Ḡ` is the three blocks' squared entries. -/
private theorem Zonotope.aux_frobSq_luenbergerUpdate (F : Mat ℝ n n) (Γ : Mat ℝ p n) (Λ : Mat ℝ n p)
    (Q : Mat ℝ n nq) (R : Mat ℝ p nr) (y : Vec ℝ p) (X : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    ∑ i, ∑ k, ((Zonotope.luenbergerUpdate F Γ Λ Q R y X).G k i) ^ 2 =
      (∑ i, ∑ k, (((F - Λ * Γ) * Matrix.of fun i j => X.G j i) i k) ^ 2) +
        (∑ i, ∑ j, ((Λ * R) i j) ^ 2) + ∑ i, ∑ j, (Q i j) ^ 2 := by -- --- PROOF ---
  have hi : ∀ i, ∑ k : Fin (X.h + nr + nq), ((Zonotope.luenbergerUpdate F Γ Λ Q R y X).G k i) ^ 2 =
      (∑ k, (((F - Λ * Γ) * Matrix.of fun i j => X.G j i) i k) ^ 2) +
        (∑ j, ((Λ * R) i j) ^ 2) + ∑ j, (Q i j) ^ 2 := by
    intro i
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.luenbergerUpdate, Fin.append_left, Fin.append_right]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.mul_apply]
  calc _ = ∑ i, ((∑ k, (((F - Λ * Γ) * Matrix.of fun i j => X.G j i) i k) ^ 2) +
        (∑ j, ((Λ * R) i j) ^ 2) + ∑ j, (Q i j) ^ 2) := Finset.sum_congr rfl fun i _ => hi i
    _ = _ := by simp only [Finset.sum_add_distrib]

/-- The cost of `X - Y` splits into the costs of `X` and `Y` and a cross term. -/
private theorem Zonotope.aux_sq_sub {a b : ℕ} (X Y : Mat ℝ a b) :
    ∑ i, ∑ j, (X i j - Y i j) ^ 2 =
      (∑ i, ∑ j, X i j ^ 2) - 2 * (∑ i, ∑ j, X i j * Y i j) + ∑ i, ∑ j, Y i j ^ 2 := by
  have : ∀ i j, (X i j - Y i j) ^ 2 = X i j ^ 2 - 2 * (X i j * Y i j) + Y i j ^ 2 :=
    fun i j => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The cost of `X + Y`, the same. -/
private theorem Zonotope.aux_sq_add {a b : ℕ} (X Y : Mat ℝ a b) :
    ∑ i, ∑ j, (X i j + Y i j) ^ 2 =
      (∑ i, ∑ j, X i j ^ 2) + 2 * (∑ i, ∑ j, X i j * Y i j) + ∑ i, ∑ j, Y i j ^ 2 := by
  have : ∀ i j, (X i j + Y i j) ^ 2 = X i j ^ 2 + 2 * (X i j * Y i j) + Y i j ^ 2 :=
    fun i j => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.luenbergerGain_optimal (F : Mat ℝ n n) (Γ : Mat ℝ p n) (Q : Mat ℝ n nq)
    (R : Mat ℝ p nr) (y : Vec ℝ p) (X : Zonotope (Vec ℝ n))
    (hS : IsUnit (Γ * (Matrix.of fun i j => X.G j i) * (Matrix.of fun i j => X.G j i)ᵀ * Γᵀ +
      R * Rᵀ).det) (Λ' : Mat ℝ n p) : -- --- CONCL ---
    ∑ i, ∑ k, ((Zonotope.luenbergerUpdate F Γ (Zonotope.luenbergerGain F Γ R X) Q R y X).G k i)
        ^ 2 ≤
      ∑ i, ∑ k, ((Zonotope.luenbergerUpdate F Γ Λ' Q R y X).G k i) ^ 2 := by -- --- PROOF ---
  rw [Zonotope.aux_frobSq_luenbergerUpdate, Zonotope.aux_frobSq_luenbergerUpdate]
  set A : Mat ℝ n X.h := Matrix.of fun i j => X.G j i with hA
  set S : Mat ℝ p p := Γ * A * Aᵀ * Γᵀ + R * Rᵀ with hSdef
  set Λ : Mat ℝ n p := Zonotope.luenbergerGain F Γ R X with hΛ
  set D : Mat ℝ n p := Λ' - Λ with hD
  -- stationarity, Eq. 34: `Λ S = F Ĝ Ĝᵀ Γᵀ`, so `(F - Λ Γ) Ĝ Ĝᵀ Γᵀ = Λ R Rᵀ`
  have hΛS : Λ * S = F * A * Aᵀ * Γᵀ := by
    rw [hΛ, Zonotope.luenbergerGain, hSdef, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]
  have hstat : (F - Λ * Γ) * A * Aᵀ * Γᵀ = Λ * R * Rᵀ := by
    have : (F - Λ * Γ) * A * Aᵀ * Γᵀ = F * A * Aᵀ * Γᵀ - Λ * (Γ * A * Aᵀ * Γᵀ) := by
      simp only [Matrix.sub_mul, Matrix.mul_assoc]
    rw [this, ← hΛS, hSdef, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  -- the two blocks at `Λ'` in terms of those at `Λ`
  have h1 : (F - Λ' * Γ) * A = (F - Λ * Γ) * A - (D * Γ) * A := by
    simp only [hD, Matrix.sub_mul]
    abel
  have h2 : Λ' * R = Λ * R + D * R := by
    simp only [hD, Matrix.sub_mul]
    abel
  -- the cross terms agree, by stationarity
  have hcross : ∑ i, ∑ j, ((F - Λ * Γ) * A) i j * ((D * Γ) * A) i j =
      ∑ i, ∑ j, (Λ * R) i j * (D * R) i j := by
    rw [Zonotope.aux_sum_mul_eq_trace, Zonotope.aux_sum_mul_eq_trace]
    have e1 : (F - Λ * Γ) * A * ((D * Γ) * A)ᵀ = ((F - Λ * Γ) * A * Aᵀ * Γᵀ) * Dᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have e2 : Λ * R * (D * R)ᵀ = (Λ * R * Rᵀ) * Dᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1, e2, hstat]
  rw [h1, h2]
  simp only [Matrix.sub_apply, Matrix.add_apply]
  rw [Zonotope.aux_sq_sub, Zonotope.aux_sq_add, hcross]
  have n1 : 0 ≤ ∑ i, ∑ j, ((D * Γ) * A) i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have n2 : 0 ≤ ∑ i, ∑ j, (D * R) i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
