module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

/-!
# The expansion of a coefficient fails for a merely smooth right-hand side

`[1, Lemma 3]` claims that for smooth `f` every coefficient `‖Aᵖ(h)G(h)‖₁,ᵢ` is either
identically `0` or `h^q ‖a + b(h)‖₁` with `a ≠ 0` and `b(h) = O(h)`. Take `n = m = 1`,
`A = 0`, `p = 0` and `G(h) = exp(-1/h)` for `h > 0`, `0` otherwise (Mathlib's
`expNegInvGlue`): smooth, positive for `h > 0`, so not zero near `0`, and under every
power of `h`, so `h^{-q} G(h) → 0` while `‖a + b(h)‖₁ → ‖a‖₁ ≠ 0`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology Matrix Polynomial


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Lemma 3]` as printed: a smooth `G` with a coefficient that is neither zero near `0` nor
`h^q` times a factor tending to a nonzero vector. -/
theorem rowNorm_expansion_counterexample : -- --- STMT ---
    ∃ (A G : ℝ → Mat ℝ 1 1), (∀ (k l : Fin 1) (n : ℕ∞), ContDiff ℝ n (fun t => A t k l)) ∧
      (∀ (k l : Fin 1) (n : ℕ∞), ContDiff ℝ n (fun t => G t k l)) ∧
      ¬ ((∀ᶠ t in 𝓝 (0:ℝ), ∑ j, |(A t ^ 0 * G t) 0 j| = 0) ∨
        ∃ (q : ℕ) (a : Vec ℝ 1) (b : ℝ → Vec ℝ 1), a ≠ 0 ∧ b 0 = 0 ∧ b =O[𝓝 0] (fun t => t) ∧
          ContinuousAt (fun t => ∑ j, |a j + b t j|) 0 ∧
          ∀ᶠ t in 𝓝[≥] (0:ℝ),
            ∑ j, |(A t ^ 0 * G t) 0 j| = t ^ q * ∑ j, |a j + b t j|) := by -- --- PROOF ---
  refine ⟨fun _ => 0, fun t => !![expNegInvGlue t], fun k l n => contDiff_const,
    fun k l n => ?_, ?_⟩
  · fin_cases k; fin_cases l
    simpa using expNegInvGlue.contDiff (n := n)
  · rintro (h | ⟨q, a, b, ha, -, hb, -, hev⟩)
    -- positive on the right of `0`, so not zero near `0`
    · have h' : ∀ᶠ t in 𝓝[>] (0:ℝ), expNegInvGlue t = 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds h] with t ht
        simpa using ht
      obtain ⟨t, ht, ht0⟩ := (h'.and self_mem_nhdsWithin).exists
      exact absurd ht (expNegInvGlue.pos_of_pos ht0).ne'
    · have ha0 : a 0 ≠ 0 := fun h0 => ha (funext fun j => by fin_cases j; simpa using h0)
      -- `b → 0`
      have h1 : Tendsto b (𝓝 (0:ℝ)) (𝓝 0) := hb.trans_tendsto tendsto_id
      have h2 : Tendsto (fun t => b t 0) (𝓝 (0:ℝ)) (𝓝 0) :=
        ((continuous_apply (0 : Fin 1)).tendsto (0 : Vec ℝ 1)).comp h1
      have hb0 : Tendsto (fun t => b t 0) (𝓝[>] (0:ℝ)) (𝓝 0) := h2.mono_left nhdsWithin_le_nhds
      -- `|a 0 + b t 0| → |a 0|`
      have hlim1 : Tendsto (fun t => |a 0 + b t 0|) (𝓝[>] (0:ℝ)) (𝓝 |a 0|) := by
        simpa using (tendsto_const_nhds.add hb0).abs
      -- while it equals `t⁻¹ ^ q * g t → 0`
      have hev' : ∀ᶠ t in 𝓝[>] (0:ℝ), expNegInvGlue t = t ^ q * |a 0 + b t 0| := by
        filter_upwards [nhdsWithin_mono _ Set.Ioi_subset_Ici_self hev] with t ht
        have := by simpa [Fin.sum_univ_one] using ht
        rwa [abs_of_nonneg (expNegInvGlue.nonneg t)] at this
      have hlim2 : Tendsto (fun t : ℝ => |a 0 + b t 0|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have h0 : Tendsto (fun x : ℝ => (X ^ q : ℝ[X]).eval x⁻¹ * expNegInvGlue x)
            (𝓝 0) (𝓝 0) := expNegInvGlue.tendsto_polynomial_inv_mul_zero _
        refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [hev', self_mem_nhdsWithin] with t ht ht0
        have htne : t ≠ 0 := ht0.ne'
        rw [ht]
        simp only [eval_pow, eval_X, inv_pow]
        field_simp
      exact ha0 (abs_eq_zero.mp (tendsto_nhds_unique hlim1 hlim2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
