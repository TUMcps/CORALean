module

public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.reachGuard`: [1, Alg. 1], the reachable set within a location and at a guard

[1, Alg. 1], "Compute `R'_j` within a location `z_i`", one `let` per printed line. Its four
operators are arguments: `reach` gives `R([kr, (k+1)r])` at `k`, `halfspaceConv` and
`generatorConv` are the over-approximative conversions of [1, Prop. 9], [1, Thm. 7] and
[1, Prop. 12], `intersectionTimes` the first and last position that may meet the guard, and
`isEmpty` the test `R^H = ∅`. `Location.IsTrajectory.reachGuard_outer` states what each must
guarantee. Two readings of the listing: the loop runs while `R^H ≠ ∅` and `t < t_f`, where it
prints "or"; `t`, never assigned, is `kr`. Times are in steps. Generic over the representations
and the scalar.

## Inputs
* `ℓ` – location
* `e` – transition
* `reach` – reach set at a step
* `halfspaceConv` – conversion to a guard set
* `isEmpty` – emptiness test
* `intersectionTimes` – first and last step meeting the guard
* `generatorConv` – conversion back to a state set
* `N` – number of steps

## Output
* guard sets up to the exit and the set there

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems,
      2010.](../../../../references/2010/althoff-nahs-zonotopes-polytopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: `R^H([0, t^end_inv])`, as the list of its pieces, and `R_j`, the enclosure
of where it meets the guard of `e`, for `t_f = N r`. -/
def Location.reachGuard [∀ n, Intersection (G n) (Vec ℝ n)] (ℓ : Location S G L 𝕋 n)
    (e : Transition G L 𝕋 n) (reach : ℕ → S n) (halfspaceConv : S n → G n)
    (isEmpty : G n → Bool) (intersectionTimes : List (G n) → G n → ℕ × ℕ)
    (generatorConv : List (G n) → S n) (N : ℕ) : List (G n) × S n :=
  -- 1. `R([(k-1)r, kr]) ← reach(…)`, `R^H([(k-1)r, kr]) ← halfspaceConv(R([(k-1)r, kr])) ∩ inv`
  let RH : ℕ → G n := fun k => Intersection.intersection (halfspaceConv (reach (k - 1))) ℓ.inv
  -- 2. `k := 1; while R^H([(k-1)r, kr]) ≠ ∅ and kr < t_f do … k := k + 1`, at most N passes
  let k := (fun k => if !isEmpty (RH k) && decide (k < N) then k + 1 else k)^[N] 1
  -- 3. `t^end_inv ← (k - 1) r`
  let tEnd := k - 1
  -- 4. `R^H([0, t^end_inv])`, the union of the `R^H([(i-1)r, ir])`
  let RH₀ := (List.range tEnd).map fun i => RH (i + 1)
  -- 5. `[t^start_g, t^end_g] ←` the first and last time `R^H([0, t^end_inv])` meets `g`
  let tg := intersectionTimes RH₀ e.guard
  -- 6. `R_j ← generatorConv(R^H([t^start_g, t^end_g]) ∩ g)`
  let Rj := generatorConv (((List.range tEnd).filter fun i => tg.1 ≤ i ∧ i ≤ tg.2).map
    fun i => Intersection.intersection (RH (i + 1)) e.guard)
  (RH₀, Rj)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
