module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# Taylor's theorem with the Lagrange remainder, in several variables

For `f : ℝⁿ → ℝ` of class `C^{N+1}` and `c`, `x` in a convex set `C`, the order-`N` expansion
of `f` at `c`, written with iterated Fréchet derivatives `Dᵏf(c)(x - c, …, x - c) / k!`, is off
by the next term evaluated at some `ξ ∈ C` — `((x - c)ᵀ∇)^{N+1} f(ξ) / (N+1)!` in [1, Def. 7]'s
notation. Read off the one-variable theorem along the segment `t ↦ c + t (x - c)`, whose `k`-th
derivative is `Dᵏf` applied to `x - c` in every slot; `ξ` lies on the segment, hence in `C`.

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

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Along a line, the `i`-th derivative is the `i`-th Fréchet derivative in the line's
direction. -/
theorem aux_iteratedDeriv_line {f : Vec ℝ n → ℝ} {N : ℕ} (hf : ContDiff ℝ N f)
    (c v : Vec ℝ n) {i : ℕ} (hi : i ≤ N) (t : ℝ) :
    iteratedDeriv i (fun t : ℝ => f (c + t • v)) t
      = iteratedFDeriv ℝ i f (c + t • v) (fun _ => v) := by -- --- PROOF ---
  let L : ℝ →L[ℝ] Vec ℝ n := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  have hcomp : (fun t : ℝ => f (c + t • v)) = (fun z => f (c + z)) ∘ L := by
    funext t; simp [L]
  have hf' : ContDiff ℝ N (fun z => f (c + z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp,
    L.iteratedFDeriv_comp_right hf' t (by exact_mod_cast hi),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp [L]


-- =======================================  MAIN THEOREM  ======================================= --

theorem taylor_lagrange_convex {f : Vec ℝ n → ℝ} {N : ℕ} (hf : ContDiff ℝ (N + 1) f)
    {C : Set (Vec ℝ n)} (hC : Convex ℝ C) {c x : Vec ℝ n} (hc : c ∈ C) (hx : x ∈ C) :
    ∃ ξ ∈ C, f x = ∑ k ∈ Finset.range (N + 1),
        iteratedFDeriv ℝ k f c (fun _ => x - c) / (k.factorial : ℝ)
      + iteratedFDeriv ℝ (N + 1) f ξ (fun _ => x - c)
        / ((N + 1).factorial : ℝ) := by -- --- PROOF ---
  set v := x - c with hv
  have hg : ContDiff ℝ (N + 1) (fun t : ℝ => f (c + t • v)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  obtain ⟨t, ht, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := fun t : ℝ => f (c + t • v)) (x₀ := 0) (x := 1) (n := N) zero_ne_one hg.contDiffOn
  have hI : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by rw [hI]; exact uniqueDiffOn_Icc zero_lt_one
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := Set.left_mem_uIcc
  -- the within-the-segment Taylor polynomial is the global one, read in `f`'s derivatives
  have htay : taylorWithinEval (fun t : ℝ => f (c + t • v)) N (Set.uIcc 0 1) 0 1
      = ∑ k ∈ Finset.range (N + 1), iteratedFDeriv ℝ k f c (fun _ => v) / (k.factorial : ℝ) := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N + 1 := by have := Finset.mem_range.1 hk; omega
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hg.contDiffAt.of_le (by exact_mod_cast hk')) h0,
      aux_iteratedDeriv_line hf c v (by exact_mod_cast hk') 0]
    simp [div_eq_inv_mul]
  -- the mean-value point lies on the segment, hence in `C`
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← hI]; exact Set.uIoo_subset_uIcc_self ht
  refine ⟨c + t • v, hC.add_smul_sub_mem hc hx ht', ?_⟩
  rw [htay, aux_iteratedDeriv_line hf c v le_rfl t] at h
  have hx' : c + (1 : ℝ) • v = x := by simp [hv]
  simp only [hx', sub_zero, one_pow, mul_one] at h
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
