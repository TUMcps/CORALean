module

public import CORALean.Specification.Operations.VerifyHalfspace
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `[1, Sec. 5.1 (termination)]`: the repaired `Alg. 2` falsifies a violation with a margin

`verifyHalfspace` from round `0` answers `unsafe` once its `fuel` reaches some round, provided a
state of `R` exceeds an offset by a margin `m > 0`, every round's upper bounds bound every state
of `R` at some step, and the lower bounds converge: from some round on, each value `R` reaches is
within `ε` of some step's lower bound. That is the argument of [1, Sec. 5.1 (termination)], made
for the repaired order. The convergence of the bounds of `Alg. 1` is the hypothesis `hconv`, not a
theorem of the tree.

## Inputs
* `ℓ` – directions
* `d` – offsets
* `R` – reachable set
* `bndUp` – upper bounds per round, step and direction
* `bndLo` – lower bounds per round, step and direction
* `m` – margin

## Hypotheses
* `hm` – the margin is positive
* `hmargin` – some state of `R` exceeds some offset by the margin
* `hup` – every state of `R` is under the upper bounds of some step of each round
* `hconv` – the lower bounds converge to every value `R` reaches, uniformly in the direction

## Conclusion
* from some fuel on, the search answers unsafe

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

/-- `[1, Sec. 5.1 (termination)]`: with a violation by a margin, sound upper bounds and converging
lower bounds, `verifyHalfspace` answers `unsafe` for all large enough `fuel`. -/
theorem verifyHalfspace_eq_violated_of_margin {ℓ : ι → α →ₗ[ℝ] ℝ} {d : ι → ℝ} {R : Set α}
    {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ} {m : ℝ} (hm : 0 < m)
    (hmargin : ∃ x ∈ R, ∃ i, d i + m ≤ ℓ i x)
    (hup : ∀ r, ∀ x ∈ R, ∃ k, ∀ i, ℓ i x ≤ bndUp r k i)
    (hconv : ∀ ε > 0, ∃ r₀, ∀ r ≥ r₀, ∀ x ∈ R, ∀ i, ∃ k,
      ℓ i x ≤ bndLo r k i + ε) : -- --- CONCL ---
    ∃ r₀ : ℕ, ∀ fuel ≥ r₀, verifyHalfspace bndUp bndLo d 0 fuel = .violated := by -- --- PROOF ---
  obtain ⟨x, hx, i, hxi⟩ := hmargin
  obtain ⟨r₀, hr₀⟩ := hconv (m / 2) (by positivity)
  -- no round verifies: some step's upper bound reaches the violating state
  have hnv : ∀ r, ¬ ∀ (k : Fin (2 ^ r)) (i : ι), bndUp r k i ≤ d i := by
    intro r hall
    obtain ⟨k, hk⟩ := hup r x hx
    linarith [hall k i, hk i]
  -- from round `r₀` on, some step's lower bound clears the offset
  have hf : ∀ r ≥ r₀, ∃ (k : Fin (2 ^ r)) (i : ι), d i < bndLo r k i := by
    intro r hr
    obtain ⟨k, hk⟩ := hr₀ r hr x hx i
    exact ⟨k, i, by linarith⟩
  -- a round from which `fuel` reaches `r₀` answers `unsafe`
  have key : ∀ fuel r : ℕ, r₀ ≤ r + fuel →
      verifyHalfspace bndUp bndLo d r fuel = .violated := by
    intro fuel
    induction fuel with
    | zero =>
      intro r hr
      simp only [verifyHalfspace]
      rw [if_pos (hf r (by omega))]
    | succ fuel ih =>
      intro r hr
      simp only [verifyHalfspace]
      split_ifs with h1 h2
      · rfl
      · exact absurd h2 (hnv r)
      · exact ih (r + 1) (by omega)
  exact ⟨r₀, fun fuel hf => key fuel 0 (by omega)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
