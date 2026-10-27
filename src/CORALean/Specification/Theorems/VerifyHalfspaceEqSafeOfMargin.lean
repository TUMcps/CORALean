module

public import CORALean.Specification.Operations.VerifyHalfspace
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `[1, Sec. 5.1 (termination)]`: the repaired `Alg. 2` verifies a safe set with a margin

`verifyHalfspace` from round `0` answers `safe` once its `fuel` reaches some round, provided `R`
keeps a margin `m > 0` from every offset, every lower bound is a value `R` reaches, and the upper
bounds converge: from some round on, each lies within `ε` of a value `R` reaches. That is the
argument of [1, Sec. 5.1 (termination)], made for the repaired order. The convergence of the
bounds of `Alg. 1` as `Δt` halves is the hypothesis `hconv` here, not a theorem of the tree.

## Inputs
* `ℓ` – directions
* `d` – offsets
* `R` – reachable set
* `bndUp` – upper bounds per round, step and direction
* `bndLo` – lower bounds per round, step and direction
* `m` – margin

## Hypotheses
* `hm` – the margin is positive
* `hmargin` – every state of `R` keeps the margin from every offset
* `hlo` – every lower bound is at most a value `R` reaches
* `hconv` – the upper bounds converge to values `R` reaches, uniformly in step and direction

## Conclusion
* from some fuel on, the search answers safe

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α ι : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Sec. 5.1 (termination)]`: with a margin from every offset, sound lower bounds and
converging upper bounds, `verifyHalfspace` answers `safe` for all large enough `fuel`. -/
theorem verifyHalfspace_eq_safe_of_margin {ℓ : ι → α →ₗ[ℝ] ℝ} {d : ι → ℝ} {R : Set α}
    {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ} {m : ℝ} (hm : 0 < m)
    (hmargin : ∀ x ∈ R, ∀ i, ℓ i x + m ≤ d i)
    (hlo : ∀ r k i, ∃ x ∈ R, bndLo r k i ≤ ℓ i x)
    (hconv : ∀ ε > 0, ∃ r₀, ∀ r ≥ r₀, ∀ k i, ∃ x ∈ R, bndUp r k i ≤ ℓ i x + ε) : -- --- CONCL ---
    ∃ r₀ : ℕ, ∀ fuel ≥ r₀, verifyHalfspace bndUp bndLo d 0 fuel = .safe := by -- --- PROOF ---
  obtain ⟨r₀, hr₀⟩ := hconv m hm
  -- no lower bound clears its offset: it is a value of `R`, which stays `m` below
  have hnf : ∀ r, ¬ ∃ (k : Fin (2 ^ r)) (i : ι), d i < bndLo r k i := by
    rintro r ⟨k, i, hlt⟩
    obtain ⟨x, hx, hle⟩ := hlo r k i
    linarith [hmargin x hx i]
  -- from round `r₀` on, every upper bound is under its offset
  have hv : ∀ r ≥ r₀, ∀ (k : Fin (2 ^ r)) (i : ι), bndUp r k i ≤ d i := by
    intro r hr k i
    obtain ⟨x, hx, hle⟩ := hr₀ r hr k i
    linarith [hmargin x hx i]
  -- a round from which `fuel` reaches `r₀` answers `safe`
  have key : ∀ fuel r : ℕ, r₀ ≤ r + fuel → verifyHalfspace bndUp bndLo d r fuel = .safe := by
    intro fuel
    induction fuel with
    | zero =>
      intro r hr
      simp only [verifyHalfspace]
      rw [if_neg (hnf r), if_pos (hv r (by omega))]
    | succ fuel ih =>
      intro r hr
      simp only [verifyHalfspace]
      rw [if_neg (hnf r)]
      split_ifs
      · rfl
      · exact ih (r + 1) (by omega)
  exact ⟨r₀, fun fuel hf => key fuel 0 (by omega)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
