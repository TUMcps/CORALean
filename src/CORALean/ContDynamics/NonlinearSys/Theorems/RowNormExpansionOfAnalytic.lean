import CORALean.Global.Tensor
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The expansion of a coefficient of the error series

`[1, Lemma 3]`: each coefficient `‖Aᵖ(h)G(h)‖₁,ᵢ` of `[1, (35)]` either vanishes
near `0` or equals `h^{q⁽ᵖ⁾ᵢ}‖a⁽ᵖ⁾ᵢ + b⁽ᵖ⁾ᵢ(h)‖₁` with `a⁽ᵖ⁾ᵢ ≠ 0` and
`b⁽ᵖ⁾ᵢ(h) = O(h)`. `Q⁽ᵖ⁾ᵢ(h) = ‖a⁽ᵖ⁾ᵢ + b⁽ᵖ⁾ᵢ(h)‖₁` is then non-negative, being
a sum of absolute values, and continuous at `0` — the regularity `[1, Thm. 2]`
and `[1, Prop. 2]` read off it, in place of `[1]`'s "piecewise smooth".

**Analytic, where `[1]` says smooth.** The dichotomy is false for a merely smooth `f`:
`h ↦ exp(-1/h²)`, extended by `0`, is smooth, vanishes nowhere but at `0`, and is under
`h^q` for every `q`, so it is neither alternative. `[1]`'s proof reads "every Taylor
coefficient of `[Aᵖ(h)G(h)]ᵢ` vanishes" as `[Aᵖ(h)G(h)]ᵢ ≡ 0`, which is what analyticity
buys and smoothness does not; see the paper page's finding. Analyticity is asked of the
entries, so nothing has to put a norm on `Mat ℝ`.

`≡ 0` is read as vanishing near `0`, which is all the limit `h → 0` uses and all
`AnalyticAt` can give; `a⁽ᵖ⁾ᵢ` is a vector of `m` generator coefficients rather than
`[1, (36)]`'s scalar, `‖·‖₁` there being the 1-norm of a row of `Aᵖ(h)G(h)`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A power of an entrywise analytic matrix is entrywise analytic: each entry is
a finite sum of products of entries. -/
theorem aux_analyticAt_pow_entry (A : ℝ → Mat ℝ n n)
    (hA : ∀ k l, AnalyticAt ℝ (fun t => A t k l) 0) (p : ℕ) (k l : Fin n) :
    AnalyticAt ℝ (fun t => (A t ^ p) k l) 0 := by -- --- PROOF ---
  induction p generalizing k l with
  | zero => simpa using analyticAt_const
  | succ p ih =>
    -- peel one factor off the back, so that the entry becomes a sum over the shared index
    have hentry : ∀ t : ℝ, (A t ^ (p + 1)) k l = ∑ r, (A t ^ p) k r * A t r l := by
      intro t; rw [pow_succ, Matrix.mul_apply]
    simp only [hentry]
    exact (Finset.analyticAt_sum Finset.univ fun r _ => (ih k r).mul (hA r l)).congr
      (by filter_upwards with t; simp [Finset.sum_apply])

/-- The `i`-th row of `Aᵖ(h)G(h)`, read as a vector-valued function of `h`, is
analytic at `0`. -/
theorem aux_analyticAt_row (A : ℝ → Mat ℝ n n) (G : ℝ → Mat ℝ n m)
    (hA : ∀ k l, AnalyticAt ℝ (fun t => A t k l) 0)
    (hG : ∀ k l, AnalyticAt ℝ (fun t => G t k l) 0) (p : ℕ) (i : Fin n) :
    AnalyticAt ℝ (fun t => (fun j => (A t ^ p * G t) i j : Vec ℝ m)) 0 := by -- --- PROOF ---
  refine AnalyticAt.pi fun j => ?_
  -- one entry of the product is again a sum over the shared index
  have hentry : ∀ t : ℝ, (A t ^ p * G t) i j = ∑ r, (A t ^ p) i r * G t r j := by
    intro t; rw [Matrix.mul_apply]
  simp only [hentry]
  exact (Finset.analyticAt_sum Finset.univ
    fun r _ => (aux_analyticAt_pow_entry A hA p i r).mul (hG r j)).congr
      (by filter_upwards with t; simp [Finset.sum_apply])


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Lemma 3]` at an analytic right-hand side: a coefficient of `[1, (35)]`
vanishes near `0`, or is `h^q` times a continuous non-vanishing factor. -/
theorem rowNorm_expansion_of_analytic (A : ℝ → Mat ℝ n n) (G : ℝ → Mat ℝ n m)
    (hA : ∀ k l, AnalyticAt ℝ (fun t => A t k l) 0)
    (hG : ∀ k l, AnalyticAt ℝ (fun t => G t k l) 0) (p : ℕ) (i : Fin n) :
    (∀ᶠ t in 𝓝 (0:ℝ), ∑ j, |(A t ^ p * G t) i j| = 0) ∨
      ∃ (q : ℕ) (a : Vec ℝ m) (b : ℝ → Vec ℝ m), a ≠ 0 ∧ b 0 = 0 ∧ b =O[𝓝 0] (fun t => t) ∧
        ContinuousAt (fun t => ∑ j, |a j + b t j|) 0 ∧
        ∀ᶠ t in 𝓝[≥] (0:ℝ),
          ∑ j, |(A t ^ p * G t) i j| = t ^ q * ∑ j, |a j + b t j| := by -- --- PROOF ---
  set v : ℝ → Vec ℝ m := fun t => fun j => (A t ^ p * G t) i j with hvd
  have hva : AnalyticAt ℝ v 0 := aux_analyticAt_row A G hA hG p i
  by_cases hz : ∀ᶠ t in 𝓝 (0:ℝ), v t = 0
  · -- the row vanishes near `0`, and so does its 1-norm
    refine Or.inl ?_
    filter_upwards [hz] with t ht
    have hj : ∀ j, (A t ^ p * G t) i j = 0 := fun j => congrFun ht j
    simp [hj]
  · -- otherwise Mathlib's order of vanishing splits off `t^q` with an analytic remainder
    right
    obtain ⟨q, g, hg, hg0, hgeq⟩ := hva.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
    refine ⟨q, g 0, fun t => g t - g 0, hg0, by simp, ?_, ?_, ?_⟩
    · -- an analytic function is differentiable, so its increment is `O(h)`
      simpa using hg.differentiableAt.isBigO_sub
    · have hs : Continuous (fun x : Vec ℝ m => ∑ j, |x j|) :=
        continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).abs
      have hc : ContinuousAt (fun t => ∑ j, |g t j|) 0 := hs.continuousAt.comp hg.continuousAt
      simpa using hc
    · have hgeq' : ∀ᶠ t in 𝓝[≥] (0:ℝ), v t = (t - 0) ^ q • g t :=
        hgeq.filter_mono nhdsWithin_le_nhds
      filter_upwards [hgeq', self_mem_nhdsWithin] with t ht ht0'
      have ht0 : (0:ℝ) ≤ t := ht0'
      have hvj : ∀ j, (A t ^ p * G t) i j = t ^ q * g t j := by
        intro j
        have hj := congrFun ht j
        simpa using hj
      -- `t ≥ 0`, so `|t^q|` is `t^q` and comes out of the sum
      simp only [hvj]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 q)]
      simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
