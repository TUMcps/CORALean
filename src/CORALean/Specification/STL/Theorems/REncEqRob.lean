import CORALean.Specification.STL.Theorems.UntilDecompIff
import CORALean.Specification.STL.Theorems.UntilRobNonstrictLeIff
import CORALean.Specification.STL.Operations.DFormulaBound

/-!
# The robust encoding computes the robustness

[1, Sec. V (correctness)]: the constraints enforce `r^φ_t = ρ^φ(x, t)`, the temporal
operators encoded as in [1, Sec. IV-B.3 (temporal)], the `sup` and `inf` of the unbounded until
being `max` and `min` on a finite trajectory. True for the non-strict unbounded until and
`t + bound(φ) ≤ N`, as for the Boolean encoding; with the printed recursion it fails,
`STL.DFormula.rEnc_counterexample`. The until case compares thresholds: `m` lies below both
sides iff `φ₂` reaches `m` at some `t' ∈ [t+a, t+b]` and `φ₁` on `[t, t']`, by
`STL.until_decomp_iff` for the predicates `m ≤ ·`.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.DFormula.rEnc_eq_rob {N : ℕ} (x : ℕ → X) :
    ∀ (φ : STL.DFormula X) (t : ℕ), t + φ.bound ≤ N →
      φ.rEnc N true x t = φ.rob x t := by -- --- PROOF ---
  intro φ
  induction φ with
  | pred μ => intro t _; rfl
  | npred μ => intro t _; rfl
  | and φ ψ ihφ ihψ =>
    intro t ht
    simp only [STL.DFormula.bound] at ht
    simp only [STL.DFormula.rEnc, STL.DFormula.rob, ihφ t (by omega), ihψ t (by omega)]
  | or φ ψ ihφ ihψ =>
    intro t ht
    simp only [STL.DFormula.bound] at ht
    simp only [STL.DFormula.rEnc, STL.DFormula.rob, ihφ t (by omega), ihψ t (by omega)]
  | always a b hab φ ih =>
    -- within the horizon the window is `[t+a, t+b]`, and every step of it is computed
    intro t ht
    simp only [STL.DFormula.bound] at ht
    simp only [STL.DFormula.rEnc, STL.DFormula.rob]
    exact Finset.inf'_congr _ (by rw [min_eq_left (by omega), min_eq_left (by omega)])
      fun i hi => ih i (by have := (Finset.mem_Icc.mp hi).2; omega)
  | eventually a b hab φ ih =>
    intro t ht
    simp only [STL.DFormula.bound] at ht
    simp only [STL.DFormula.rEnc, STL.DFormula.rob]
    exact Finset.sup'_congr _ (by rw [min_eq_left (by omega), min_eq_left (by omega)])
      fun i hi => ih i (by have := (Finset.mem_Icc.mp hi).2; omega)
  | «until» a b hab φ ψ ihφ ihψ =>
    intro t ht
    simp only [STL.DFormula.bound] at ht
    have hA : ∀ s, s ≤ t + b → φ.rEnc N true x s = φ.rob x s := fun s hs => ihφ s (by omega)
    have hB : ∀ s, s ≤ t + b → ψ.rEnc N true x s = ψ.rob x s := fun s hs => ihψ s (by omega)
    -- both sides are characterized by the same threshold condition
    have key : ∀ m : ℝ, m ≤ (STL.DFormula.until a b hab φ ψ).rEnc N true x t ↔
        m ≤ (STL.DFormula.until a b hab φ ψ).rob x t := by
      intro m
      simp only [STL.DFormula.rEnc, STL.DFormula.rob, le_min_iff, Finset.le_inf'_iff,
        Finset.le_sup'_iff, STL.le_untilRob_nonstrict_iff, min_eq_left (show t ≤ N by omega),
        min_eq_left (show t + a ≤ N by omega), min_eq_left (show t + b ≤ N by omega)]
      rw [and_assoc, STL.until_decomp_iff hab (by omega)]
      constructor
      · rintro ⟨t', ht', hB', hA'⟩
        have htb := (Finset.mem_Icc.mp ht').2
        refine ⟨⟨t', ht'⟩, Finset.mem_attach _ _, by rwa [← hB t' htb], fun s hs => ?_⟩
        have hst : s ≤ t' := (Finset.mem_Icc.mp hs).2
        rw [← hA s (by omega)]
        exact hA' s hs
      -- the robustness's witness is the encoding's, the values agreeing on `[t, t+b]`
      · rintro ⟨⟨t', ht'⟩, -, hB', hA'⟩
        have htb := (Finset.mem_Icc.mp ht').2
        refine ⟨t', ht', by rwa [hB t' htb], fun s hs => ?_⟩
        rw [hA s (by have := (Finset.mem_Icc.mp hs).2; omega)]
        exact hA' s hs
    exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
