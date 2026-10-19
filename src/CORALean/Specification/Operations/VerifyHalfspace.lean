module

public import CORALean.Specification.Definitions.VerifyAnswer
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# [1, Alg. 2]: verifying a halfspace safe set, one round at a time

The decision only, over the outputs of `[1, Alg. 1 (upper bounds)]` and
`[1, Alg. 1 (lower bounds)]` taken as already-computed bounds: `bndUp`, `bndLo`, one real
per round `r` (how many times the step has halved), step `k : Fin (2 ^ r)` within it, and
direction `i`. `unsafe` fires when some step's lower bound crosses its
halfspace's offset, `safe` once every upper bound stays under it, otherwise the step halves
and the search continues on `fuel` — the honest shape of a loop `[1]` never claims
terminates. No set is built and no representation named.

The two tests are independent here. `[1, Alg. 2]` prints the falsification one as an
`else if` under the safety one, which no run reaches: a lower bound never exceeds an upper
one, so `return unsafe` is dead code and the printed loop only proves safety. Its page says so.

Real-only, a specification: it decides by quantifiers over tables of bounds supplied as arguments,
so no arithmetic is run here.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- `[1, Alg. 2]` at round `r`, `Δt = t_end / 2 ^ r`, over every direction at once; line 6's bounds
are `bndUp`, `bndLo`: `unsafe` once a lower one clears its offset, `safe` once every upper one
stays under it, else the step halves and the search continues on `fuel`. -/
noncomputable def verifyHalfspace {ι : Type} (bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ)
    (d : ι → ℝ) : ℕ → ℕ → VerifyAnswer
  | r, 0 =>
      -- 9. some step `k` and row `i` with `ρ(Ř(τₖ), ℓᵢ) > f(i)`: `return unsafe`
      let falsified := ∃ (k : Fin (2 ^ r)) (i : ι), d i < bndLo r k i
      -- 7. every `ρ(R̂(τₖ), ℓᵢ) > f(i)` fails, so `verified` stays `true`
      let verified := ∀ (k : Fin (2 ^ r)) (i : ι), bndUp r k i ≤ d i
      if falsified then .violated
      else if verified then .safe
      else .undecided
  | r, fuel + 1 =>
      -- 9. some step `k` and row `i` with `ρ(Ř(τₖ), ℓᵢ) > f(i)`: `return unsafe`
      let falsified := ∃ (k : Fin (2 ^ r)) (i : ι), d i < bndLo r k i
      -- 7. no `ρ(R̂(τₖ), ℓᵢ) > f(i)`, so `verified = true` ends the `repeat`
      let verified := ∀ (k : Fin (2 ^ r)) (i : ι), bndUp r k i ≤ d i
      if falsified then .violated
      -- 16. `return safe`
      else if verified then .safe
      -- 13. `Δt ← 0.5 Δt`
      else verifyHalfspace bndUp bndLo d (r + 1) fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
