import CORALean.Global.Mathlib

/-!
# [1, Alg. 2]: verifying a halfspace safe set, one round at a time

The decision only, over `[1, Alg. 1]`'s outputs taken as already-computed bounds: `bndUp`,
`bndLo`, one real per round `r` (how many times the step has halved), step `k : Fin (2 ^ r)`
within it, and direction `i`. `unsafe` fires when some step's lower bound crosses its
halfspace's offset, `safe` once every upper bound stays under it, otherwise the step halves
and the search continues on `fuel` — the honest shape of a loop `[1]` never claims
terminates. No set is built and no representation named.

The two tests are independent here. `[1, Alg. 2]` prints the falsification one as an
`else if` under the safety one, which no run reaches: a lower bound never exceeds an upper
one, so `return unsafe` is dead code and the printed loop only proves safety. Its page says so.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

/-- What one run of `[1, Alg. 2]` concludes: the safe set holds throughout, a point of the
reachable set already falls outside it, or `fuel` ran out with neither settled. -/
inductive VerifyAnswer
  | safe
  | «unsafe»
  | undecided


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- `[1, Alg. 2]`: at round `r`, `2 ^ r` steps and every direction at once — `unsafe` the
moment some lower bound clears its offset, `safe` once every upper bound stays under it,
otherwise the step halves and the search continues on `fuel`. -/
noncomputable def verifyHalfspace {ι : Type} (bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ)
    (d : ι → ℝ) : ℕ → ℕ → VerifyAnswer
  | r, 0 =>
      if ∃ (k : Fin (2 ^ r)) (i : ι), d i < bndLo r k i then .«unsafe»
      else if ∀ (k : Fin (2 ^ r)) (i : ι), bndUp r k i ≤ d i then .safe
      else .undecided
  | r, fuel + 1 =>
      if ∃ (k : Fin (2 ^ r)) (i : ι), d i < bndLo r k i then .«unsafe»
      else if ∀ (k : Fin (2 ^ r)) (i : ι), bndUp r k i ≤ d i then .safe
      else verifyHalfspace bndUp bndLo d (r + 1) fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
