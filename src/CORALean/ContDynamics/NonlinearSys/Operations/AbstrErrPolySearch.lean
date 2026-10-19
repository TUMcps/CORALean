module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinStep
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfPoly

@[expose] public section

/-!
# Searching for an applied error the certificate accepts

CORA's `linReach` while loop for `alg = 'poly'`, and the repeat-until of [1, Alg. 1],
its lines 8-16: `priv_abstrerr_poly` estimates the true error against an applied one,
and a rejection multiplies the applied error by `1.1` and retries —
`perfIndCurr = max(trueError ./ appliedError) ≤ 1` the test.

That test is `PolyAbstractionError` itself, already landed: `AbstractionError.of_poly`
already proves a step meeting it a sound enclosure, so nothing new is proved about
acceptance — the return type below is the proof. Any `some step` carries `step.cert`,
so a wrong `Ws k` costs no soundness, only convergence, as a wrong pivot costs
`dualCandidate` nothing but a `none`.

What is new is only the search: package the first candidate the certificate accepts
into a `LinStep`, `none` once `fuel` runs out — `minkDiffRep`'s shape. A candidate is a
region `pZ k`, its sub-box and static error as well as `Ws k`, since CORA's `Rmax`
grows with the applied error; `aux_abstrErrPolyCandidates` computes them.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

open scoped Classical in
/-- The first `k ≥ k₀` where `P` holds, tried within `fuel` rounds; `none` once
`fuel` runs out with none accepted. -/
noncomputable def aux_search (P : ℕ → Prop) : ℕ → ℕ → Option {k // P k}
  | _, 0 => none
  | k, fuel + 1 => if h : P k then some ⟨k, h⟩ else aux_search P (k + 1) fuel


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first candidate `(pZ k, Ba k, L k, Ws k)` a `PolyAbstractionError` accepts,
packaged as a `LinStep`; `none` once `fuel` is exhausted with none accepted. -/
noncomputable def NonlinearSys.abstrErrPolySearch (sys : NonlinearSys n m)
    (U : PolyZonotope (Vec ℝ m)) (A : Mat ℝ n n) (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m)
    (pZ : ℕ → PolyZonotope (Vec ℝ n)) (Ba : ∀ k, Set (Fin (pZ k).p → ℝ))
    (L : ℕ → PolyZonotope (Vec ℝ n)) (hp : ∀ k, (L k).p = (pZ k).p)
    (hBa : ∀ k, ∀ a ∈ Ba k, ∀ j, |a j| ≤ 1) (Ws : ℕ → PolyZonotope (Vec ℝ n))
    (fuel : ℕ) : Option (sys.LinStep (S := 𝒫𝒵) U) :=
  (aux_search (fun k => PolyAbstractionError sys.f A B xs us (pZ k) (Ba k) (construct U) (L k)
      (hp k) (Ws k)) 0 fuel).map
    fun ⟨k, h⟩ => ⟨A, B, xs, us, (pZ k).subsetAt (Ba k), L k ⊞ Ws k,
      AbstractionError.of_poly (hBa k) h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
