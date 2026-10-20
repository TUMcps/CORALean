module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# The determinant of a matrix exponential

`det(e^{tA}) = e^{t tr(A)}`, the formula `[1, Prop. 3]` calls well known. Mathlib has none.
`g(t) = det(e^{tA})` has derivative `tr(A)` at `0` (the permutation expansion of `det`, whose
product rule keeps only the identity permutation at `e^{0} = I`), it is multiplicative, so
`g' = tr(A) g` everywhere, and `g(t) e^{-t tr(A)}` has derivative `0`.

## Inputs
* `A` – matrix
* `t` – time

## Hypotheses
* none

## Conclusion
* the determinant of the exponential is the exponential of time times the trace

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The entries of `e^{tA}` have derivative `A` at `t = 0`. -/
theorem aux_hasDerivAt_exp_entry (A : Mat ℝ n n) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (exp (t • A)) i j) (A i j) 0 := by
  have h := hasDerivAt_exp_smul_const A (0 : ℝ)
  simp only [zero_smul, exp_zero, one_mul] at h
  have hi := (hasDerivAt_pi.mp h) i
  exact (hasDerivAt_pi.mp hi) j

/-- `d/dt det(e^{tA}) = tr(A)` at `t = 0`. -/
theorem aux_hasDerivAt_det_exp (A : Mat ℝ n n) :
    HasDerivAt (fun t : ℝ => det (exp (t • A))) (trace A) 0 := by -- --- PROOF ---
  simp only [det_apply']
  have hterm : ∀ σ : Equiv.Perm (Fin n), HasDerivAt
      (fun t : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (exp (t • A)) (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ i, (∏ j ∈ Finset.univ.erase i,
        (exp ((0:ℝ) • A)) (σ j) j) * A (σ i) i) 0 := by
    intro σ
    have := HasDerivAt.finsetProd (u := Finset.univ) (x := (0:ℝ))
      (f := fun i t => (exp (t • A)) (σ i) i) (f' := fun i => A (σ i) i)
      (fun i _ => aux_hasDerivAt_exp_entry A (σ i) i)
    simpa using this.const_mul _
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hterm σ)
  refine this.congr_deriv ?_
  simp only [zero_smul, exp_zero, one_apply]
  -- only the identity permutation survives at `e⁰ = I`
  have hprod : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n),
      (∏ j ∈ Finset.univ.erase i, (if σ j = j then (1:ℝ) else 0))
        = if σ = 1 then 1 else 0 := by
    intro σ i
    by_cases h : σ = 1
    · subst h; simp
    · rw [if_neg h]
      refine Finset.prod_eq_zero_iff.mpr ?_
      by_contra hne
      push Not at hne
      have hfix : ∀ j, j ≠ i → σ j = j := fun j hj => by
        have := hne j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
        by_contra hc
        simp [hc] at this
      apply h
      refine Equiv.ext fun k => ?_
      by_cases hk : k = i
      · subst hk
        -- the remaining point is fixed since `σ` is a bijection fixing all others
        by_contra hki
        have h2 : σ (σ k) = σ k := hfix _ hki
        exact hki (σ.injective h2)
      · simpa using hfix k hk
  simp only [hprod]
  rw [trace]
  simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.det_exp_smul (A : Mat ℝ n n) (t : ℝ) :
    det (exp (t • A)) = Real.exp (t * trace A) := by -- --- PROOF ---
  set g : ℝ → ℝ := fun t => det (exp (t • A)) with hg
  -- multiplicative: the exponents commute
  have hmul : ∀ s t, g (s + t) = g s * g t := fun s t => by
    simp only [hg]
    have hc : Commute (s • A) (t • A) := ((Commute.refl A).smul_left s).smul_right t
    have hA : exp ((s + t) • A) = exp (s • A) * exp (t • A) := by
      rw [add_smul]
      exact exp_add_of_commute hc
    rw [hA, det_mul]
  -- so the derivative everywhere is `tr(A) g`
  have hder : ∀ t, HasDerivAt g (g t * trace A) t := fun t => by
    have h0 : HasDerivAt (fun h => g t * g h) (g t * trace A) 0 :=
      (aux_hasDerivAt_det_exp A).const_mul (g t)
    have h1 := HasDerivAt.comp_sub_const t t (by simpa using h0)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show g x = g t * g (x - t)
    rw [← hmul]; congr 1; ring
  -- and `g(t) e^{-t tr(A)}` is constant
  set k : ℝ → ℝ := fun t => g t * Real.exp (-(t * trace A)) with hk
  have hkd : ∀ t, HasDerivAt k 0 t := fun t => by
    have h2 := (((hasDerivAt_id t).mul_const (trace A)).neg).exp
    refine ((hder t).mul h2).congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hkd t).differentiableAt)
    (fun t => (hkd t).deriv)
  have h0 : k t = k 0 := hconst t 0
  have hg0 : g 0 = 1 := by simp [hg]
  simp only [hk, hg0, zero_mul, neg_zero, Real.exp_zero, mul_one] at h0
  have : g t = Real.exp (t * trace A) := by
    have h3 : g t = g t * Real.exp (-(t * trace A)) * Real.exp (t * trace A) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [h3, h0, one_mul]
  exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
