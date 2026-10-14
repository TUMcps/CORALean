module

public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.reachGuard`: [1, Alg. 5], the reachable set within a location and at a guard

[1, Alg. 5], "Compute `R'_j` within a location `y_i`", one `let` per printed line. Its four
operators are arguments, as the listing leaves them to other sections of [1]: `reach` gives
`R([kr, (k+1)r])` at `k` (sections 3.2-3.4), `halfspaceConv` and `generatorConv` are the
over-approximative conversions of sections 2.5.6 and 3.5.4 (the latter enclosing several
polytopes at once), and `intersectionTimes` returns the first and last position of
`R^H([0, t^end_inv])` that may meet the guard. `isEmpty` is the test `R^H = ∅`, `true` only
when it is. `Location.Trajectory.reachGuard_outer` states what each must guarantee.

Two readings of the listing: the loop runs while `R^H([(k-1)r, kr]) ≠ ∅` *and* `t < t_f`,
where it prints "or", which would not stop before `t_f`; and `t`, never assigned, is `kr`.
At `t_f = N r` it runs at most `N - 1` times: `N` passes, a failed test leaving `k` alone.
Times are in steps, `t^end_inv = (k - 1) r` being `k - 1`; the output `R^H([0, t^end_inv])` is
the list of the `R^H([(i-1)r, ir])`, `i = 1, …, k - 1`, whose union the listing writes.

[2, Alg. 1] is the same listing, `reach` there being `R([kr, (k+1)r]) = e^{Ar}R([(k-1)r, kr]) +
R̄([0, r])`. Generic over the representations and the scalar: one definition, both layers.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
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

/-- [1, Alg. 5]: `R^H([0, t^end_inv])`, as the list of its pieces, and `R_j`, the enclosure
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
