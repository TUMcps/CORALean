module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLogDet
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLogDetHasDerivAt
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# The second derivative of the volume criterion at the root

[1, Eq. 19]: at a root `β₊` of [1, Eq. 18] the second derivative of `log det Q(β)` is
`(1/(β₊(1+β₊))) ∑ᵢ (β₊²λᵢ² + (1 + 2β₊)λᵢ)/(1 + β₊λᵢ)²`, positive for positive `λᵢ`.
Differentiating `−(1/(β(1+β))) · S(β)` the term with `S` drops at a root, and
`S'(β) = −∑ᵢ λᵢ(1 + 2β + β²λᵢ)/(1+βλᵢ)²`.

## Inputs
* `r` – root of the stationarity equation

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hr` – `0 < r`
* `hroot` – the stationarity function vanishes at `r`

## Conclusion
* the second derivative at `r` is the given sum and positive

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_stationarity_hasDerivAt (hlam : ∀ i, 0 < lam i) {β : ℝ}
    (hβ : 0 < β) : -- --- CONCL ---
    HasDerivAt (Ellipsoid.halderStationarity lam)
      (-∑ i, lam i * (1 + 2 * β + β ^ 2 * lam i) / (1 + β * lam i) ^ 2) β := by -- --- PROOF ---
  unfold Ellipsoid.halderStationarity
  -- each term is a quotient, `(1 − β²λ)/(1 + βλ)`
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt
      (fun y => (1 - y ^ 2 * lam i) / (1 + y * lam i))
      (-(lam i * (1 + 2 * β + β ^ 2 * lam i) / (1 + β * lam i) ^ 2)) β := by
    intro i _
    have hpos : 1 + β * lam i ≠ 0 := by have := hlam i; positivity
    have hn : HasDerivAt (fun y : ℝ => 1 - y ^ 2 * lam i) (-(2 * β * lam i)) β := by
      have := ((hasDerivAt_pow 2 β).mul_const (lam i)).const_sub 1
      exact this.congr_deriv (by simp)
    have hdn : HasDerivAt (fun y : ℝ => 1 + y * lam i) (lam i) β := by
      have := ((hasDerivAt_id β).mul_const (lam i)).const_add 1
      exact this.congr_deriv (by simp)
    refine (hn.div hdn hpos).congr_deriv ?_
    field_simp
    ring
  have := HasDerivAt.fun_sum hterm
  refine this.congr_deriv ?_
  simp [Finset.sum_neg_distrib]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 19]: the second derivative of the criterion at a root of [1, Eq. 18], positive. -/
theorem Ellipsoid.halderLogDet_secondDeriv [Nonempty ι] (hlam : ∀ i, 0 < lam i) {r : ℝ}
    (hr : 0 < r) (hroot : Ellipsoid.halderStationarity lam r = 0) : -- --- CONCL ---
    HasDerivAt (deriv (Ellipsoid.halderLogDet lam))
      (1 / (r * (1 + r)) * ∑ i, (r ^ 2 * lam i ^ 2 + (1 + 2 * r) * lam i) / (1 + r * lam i) ^ 2) r
    ∧ 0 < 1 / (r * (1 + r)) *
      ∑ i, (r ^ 2 * lam i ^ 2 + (1 + 2 * r) * lam i) / (1 + r * lam i) ^ 2 := by -- --- PROOF ---
  have hsum : 0 < ∑ i, (r ^ 2 * lam i ^ 2 + (1 + 2 * r) * lam i) / (1 + r * lam i) ^ 2 :=
    Finset.sum_pos (fun i _ => by have := hlam i; positivity) Finset.univ_nonempty
  -- the prefactor `−1/(β(1+β))` and its derivative
  have hq : HasDerivAt (fun β : ℝ => β * (1 + β)) (1 * (1 + r) + r * 1) r :=
    (hasDerivAt_id r).mul ((hasDerivAt_id r).const_add 1)
  have hqne : r * (1 + r) ≠ 0 := by positivity
  have hu : HasDerivAt (fun β : ℝ => -(1 / (β * (1 + β)))) ((1 + 2 * r) / (r * (1 + r)) ^ 2) r := by
    simp only [one_div]
    refine (hq.inv hqne).neg.congr_deriv ?_
    ring
  have hD := hu.mul (Ellipsoid.aux_stationarity_hasDerivAt hlam hr)
  refine ⟨?_, by positivity⟩
  refine (hD.congr_deriv ?_).congr_of_eventuallyEq ?_
  · -- at a root the product rule leaves the prefactor times the derivative
    rw [hroot, mul_zero, zero_add, neg_mul_neg]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  · -- and the derivative of the criterion is that product near the root
    filter_upwards [Ioi_mem_nhds hr] with β hβ
    exact (Ellipsoid.halderLogDet_hasDerivAt hlam hβ).deriv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
