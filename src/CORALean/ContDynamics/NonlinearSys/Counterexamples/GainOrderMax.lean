module

public import CORALean.ContDynamics.NonlinearSys.Operations.GainOrder
public import Mathlib.Data.ENat.Lattice

@[expose] public section

/-!
# Eq. (40) as a maximum makes `Def. 6`'s closing sentence false

[1, Thm. 2] prints the gain order as `q_i = max{ j ∈ ℕ₀ | Σ_{p + q^(p)_i = j} ‖a^(p)_i‖₁ ≠ 0 }`,
and `Def. 6` takes `q := min_i q_i` and says the method has zero abstraction error iff
`q = ∞`. With the maximum, one dimension and every coefficient non-zero at order `p`
(`q^(p) = 0`, `a^(p) = 1`) gives `q_i = ∞`, since the set of orders is all of `ℕ`, so
`q = ∞` while the abstraction error is non-zero. `gainOrder_eq_top_iff` proves the sentence
for the minimum, and with `Lemma 3`'s convention `q^(p)_i = ∞ → a^(p)_i = 0`, which holds
here, as a hypothesis.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* infinite gain order and vanishing coefficients are not equivalent as printed

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 6] with Eq. (40) as printed: `q := min_i max{…}` is `∞` iff all coefficients
vanish. It is not. -/
theorem gainOrder_max_eq_top_iff_counterexample : -- --- CONCL ---
    ¬ ∀ (n m : ℕ) (q : ℕ → Fin n → ℕ∞) (a : ℕ → Fin n → Vec ℝ m),
      (∀ p i, q p i = ⊤ → a p i = 0) →
      ((⨅ i, sSup {j : ℕ∞ | ∃ p : ℕ, (p : ℕ∞) + q p i = j ∧ a p i ≠ 0}) = ⊤
        ↔ ∀ p i, a p i = 0) := by -- --- PROOF ---
  intro h
  have hiff := h 1 1 (fun _ _ => 0) (fun _ _ => fun _ => 1) (fun _ _ h => absurd h (by simp))
  have hnz : ¬ ∀ (p : ℕ) (i : Fin 1), (fun _ => (1 : ℝ) : Vec ℝ 1) = 0 := fun hz => by
    have := congrFun (hz 0 0) 0
    simp at this
  refine hnz (hiff.mp ?_)
  rw [iInf_eq_top]
  intro i
  by_contra hne
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hmem : ((k + 1 : ℕ) : ℕ∞) ∈ {j : ℕ∞ | ∃ p : ℕ,
      (p : ℕ∞) + (fun (_ : ℕ) (_ : Fin 1) => (0 : ℕ∞)) p i = j
      ∧ (fun (_ : ℕ) (_ : Fin 1) => fun _ => (1 : ℝ) : ℕ → Fin 1 → Vec ℝ 1) p i ≠ 0} :=
    ⟨k + 1, by simp, fun hz => by simpa using congrFun hz 0⟩
  have hle := le_sSup hmem
  rw [← hk] at hle
  have : (k + 1 : ℕ) ≤ k := by exact_mod_cast hle
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
