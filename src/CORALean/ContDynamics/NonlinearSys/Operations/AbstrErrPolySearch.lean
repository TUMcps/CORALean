import CORALean.ContDynamics.NonlinearSys.LinStep
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfPoly

/-!
# Searching for an applied error the certificate accepts

CORA's `linReach` while loop for `alg = 'poly'`: `priv_abstrerr_poly` estimates the
true error against an applied one, and a rejection multiplies the applied error by
`1.1` and retries — `perfIndCurr = max(trueError ./ appliedError) ≤ 1` the test.

That test is `PolyAbstractionError` itself, already landed: `AbstractionError.of_poly`
already proves a step meeting it a sound enclosure, so nothing new is proved about
acceptance — the return type below is the proof. Any `some step` carries `step.cert`,
so a wrong `Ws k` costs no soundness, only convergence, as a wrong pivot costs
`dualCandidate` nothing but a `none`.

What is new is only the search: try `Ws 0, Ws 1, …`, package the first the certificate
accepts into a `LinStep`, `none` once `fuel` runs out — `minkDiffRep`'s shape. Building
`Ws` from `sys.relinDeltaReach`'s output, bounding CORA's cross terms `quadMap(Zdelta,
Z_diff, H)` by a box that grows until it fits, is the analysis this leaves undone.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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

/-- The first `Ws k` a `PolyAbstractionError` accepts, packaged as a `LinStep`;
`none` once `fuel` is exhausted with none accepted. -/
noncomputable def NonlinearSys.abstrErrPolySearch (sys : NonlinearSys n m)
    (U : PolyZonotope (Vec ℝ m)) (A : Mat ℝ n n) (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m)
    (pZ : PolyZonotope (Vec ℝ n)) (Ba : Set (Fin pZ.p → ℝ)) (L : PolyZonotope (Vec ℝ n))
    (hp : L.p = pZ.p) (hBa : ∀ a ∈ Ba, ∀ k, |a k| ≤ 1) (Ws : ℕ → PolyZonotope (Vec ℝ n))
    (fuel : ℕ) : Option (sys.LinStep (S := 𝒫𝒵) U) :=
  (aux_search
      (fun k => PolyAbstractionError sys.f A B xs us pZ Ba (construct U) L hp (Ws k)) 0 fuel).map
    fun ⟨k, h⟩ => ⟨A, B, xs, us, pZ.subsetAt Ba, L ⊞ Ws k, AbstractionError.of_poly hBa h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
