module

public import CORALean.ContSet.LevelSet.Real.Definitions.TaylorSeries
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.Global.TaylorLagrangeConvex

@[expose] public section

/-!
# The Taylor series operator encloses its function

[1, Def. 7]'s claim: `∀ x ∈ I : f(x) ∈ b + aᵀ(x - c) + v(x) ⊕ [l, u]`. Two hypotheses [1] does
not state are needed. `f` is `C^{κ+1}`: [1] asks only Lipschitz continuity, which does not even
make `a = ∇f(c)` exist. And `1 ≤ κ`: the printed expansion always carries the linear term and
sums `v` from `i = 2`, so at `κ = 0` it would count the first-order term twice — once in `aᵀ(x - c)`
and once in the Lagrange remainder of order `1`. The proof is `taylor_lagrange_convex` on the box,
with the order-`0` and order-`1` terms split off the sum.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A box with a point in it contains its center. -/
theorem aux_center_mem {I : Interval (Vec ℝ n)} {x : Vec ℝ n} (hx : x ∈ I.construct) :
    I.center ∈ I.construct := by
  intro i
  have h : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
  change I.inf i ≤ (2 : ℝ)⁻¹ * (I.inf i + I.sup i) ∧ (2 : ℝ)⁻¹ * (I.inf i + I.sup i) ≤ I.sup i
  constructor <;> linarith [h.1, h.2]

/-- The first-order term, read through the gradient's coordinates. -/
theorem aux_fderiv_eq_sum (f : Vec ℝ n → ℝ) (c v : Vec ℝ n) :
    fderiv ℝ f c v = ∑ i, taylorGrad f c i * v i := by -- --- PROOF ---
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Vec ℝ n) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem TaylorSeries.mem {f : Vec ℝ n → ℝ} {I : Interval (Vec ℝ n)} {κ : ℕ}
    (T : TaylorSeries f I κ) (hf : ContDiff ℝ (κ + 1) f) (hκ : 1 ≤ κ) {x : Vec ℝ n}
    (hx : x ∈ I.construct) :
    f x - (f I.center + ∑ i, taylorGrad f I.center i * (x i - I.center i)
      + taylorHigher f κ I.center x) ∈ Set.Icc T.l T.u := by -- --- PROOF ---
  obtain ⟨ξ, hξ, h⟩ := taylor_lagrange_convex hf (Interval.convex_construct I)
    (aux_center_mem hx) hx
  -- split the order-0 and order-1 terms off the sum; the rest is `v`
  obtain ⟨m, rfl⟩ : ∃ m, κ = m + 1 := ⟨κ - 1, by omega⟩
  have hv : taylorHigher f (m + 1) I.center x = ∑ k ∈ Finset.range m,
      iteratedFDeriv ℝ (k + 1 + 1) f I.center (fun _ => x - I.center)
        / ((k + 1 + 1).factorial : ℝ) := by
    rw [taylorHigher, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1) fun k _ => ?_
    rw [add_comm 2 k]
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
  rw [Nat.zero_add, iteratedFDeriv_one_apply] at h
  simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    div_one] at h
  rw [aux_fderiv_eq_sum] at h
  have hsum : ∑ i, taylorGrad f I.center i * (x - I.center) i
      = ∑ i, taylorGrad f I.center i * (x i - I.center i) := rfl
  -- what is left is the Lagrange term, which `[l, u]` encloses
  have hL := T.encloses _ ⟨ξ, hξ, x, hx, rfl⟩
  rw [hv]
  constructor <;> linarith [hL.1, hL.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
