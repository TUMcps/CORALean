module

public import CORALean.Specification.STL.Theorems.UntilDecompIff
public import CORALean.Specification.STL.Operations.DFormulaBound

@[expose] public section

/-!
# The Boolean encoding decides the formula

[1, Sec. IV-B.3 (correctness)]: by induction on the structure of `φ`, `z^φ_t = 1` iff `φ` holds
on the system at `t`. True for the non-strict unbounded until (`nonstrict := true`) and where the
horizon reaches every step the formula reads, `t + bound(φ) ≤ N` — the condition
[1, Sec. II-B (bound)] states for deciding satisfiability, so that the windows of
[1, Sec. IV-B.3 (temporal)] are not truncated; with the printed recursion, or past the horizon,
it fails, `STL.DFormula.zEnc_counterexample`. A step `i ≤ t + b` of an
operator at `t` has `i + bound(φ) ≤ N` for its operand, which is the induction.

## Inputs
* `N` – horizon
* `x` – trace

## Hypotheses
* none

## Conclusion
* the Boolean encoding holds iff the formula is satisfied

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

theorem STL.DFormula.zEnc_iff_sat {N : ℕ} (x : ℕ → X) : -- --- CONCL ---
    ∀ (φ : STL.DFormula X) (t : ℕ), t + φ.bound ≤ N →
      (φ.IsZEnc N true x t ↔ φ.Satisfies x t) := by -- --- PROOF ---
  intro φ
  induction φ with
  | pred μ => intro t _; exact Iff.rfl
  | npred μ => intro t _; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
    intro t ht
    simp only [STL.DFormula.bound] at ht
    exact and_congr (ihφ t (by omega)) (ihψ t (by omega))
  | or φ ψ ihφ ihψ =>
    intro t ht
    simp only [STL.DFormula.bound] at ht
    exact or_congr (ihφ t (by omega)) (ihψ t (by omega))
  | always a b hab φ ih =>
    -- within the horizon the window is `[t+a, t+b]`, and every step of it is decided
    intro t ht
    simp only [STL.DFormula.bound] at ht
    simp only [STL.DFormula.IsZEnc, STL.DFormula.Satisfies, min_eq_left (show t + a ≤ N by omega),
      min_eq_left (show t + b ≤ N by omega)]
    exact forall₂_congr fun i hi => ih i (by have := (Finset.mem_Icc.mp hi).2; omega)
  | eventually a b hab φ ih =>
    intro t ht
    simp only [STL.DFormula.bound] at ht
    simp only [STL.DFormula.IsZEnc, STL.DFormula.Satisfies, min_eq_left (show t + a ≤ N by omega),
      min_eq_left (show t + b ≤ N by omega)]
    exact exists_congr fun i => and_congr_right fun hi =>
      ih i (by have := (Finset.mem_Icc.mp hi).2; omega)
  | «until» a b hab φ ψ ihφ ihψ =>
    -- the decomposition is the bounded until, then each operand is decided on `[t, t+b]`
    intro t ht
    simp only [STL.DFormula.bound] at ht
    simp only [STL.DFormula.IsZEnc, STL.DFormula.Satisfies, min_eq_left (show t ≤ N by omega),
      min_eq_left (show t + a ≤ N by omega), min_eq_left (show t + b ≤ N by omega)]
    rw [STL.until_decomp_iff hab (by omega)]
    refine exists_congr fun t' => and_congr_right fun ht' =>
      and_congr ?_ (forall₂_congr fun s hs => ?_)
    · exact ihψ t' (by have := (Finset.mem_Icc.mp ht').2; omega)
    · exact ihφ s (by have := (Finset.mem_Icc.mp hs).2; have := (Finset.mem_Icc.mp ht').2; omega)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
