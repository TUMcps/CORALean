import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfPoly
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinDeltaReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# The polynomialization variant runs the loop already proved

What this records is that step three of CORA's `alg = 'poly'` — lines 4-18 of
[1, Alg. 1] — is not a second induction. A `PolyAbstractionError` becomes a
`LinStep` through `AbstractionError.of_poly`, and `relinReach_outer` then
applies at `𝒫𝒵` with nothing added: the chain, the per-step confinement and the
input enclosures are the ones already proved, because soundness was stated at an
arbitrary certificate rather than at the one `alg = 'lin'` computes.

The instances it takes are `Plus`, `Reduce`, `Mtimes (Mat ℝ)`, `OfInterval`
and, for the differences, `LinComb` and `Mtimes ℐ`; all six `PolyZonotope` has,
and this file fails to compile the moment one goes.

`relinDeltaReach_outer` is CORA's `Rdiff`, the differences over a step rather
than the states. What the poly certificate changes is where the run has to
stay: `subsetAt` rather than a box, the two agreeing at `pZ.q = 0` by
`subsetAt_unitBox`. `abstrErrPolySearch` is `linReach`'s while loop: a
successful search hands back a `LinStep` certified by `AbstractionError.of_poly`.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   13-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Plus

-- Anonymous, since their content is that they elaborate.

/-- A certificate over the factors is one linearization step of the loop. -/
example {n m : ℕ} (sys : NonlinearSys n m) (U : PolyZonotope (Vec ℝ m)) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m) (pZ L W : PolyZonotope (Vec ℝ n))
    (Ba : Set (Fin pZ.p → ℝ)) (hp : L.p = pZ.p) (hBa : ∀ a ∈ Ba, ∀ k, |a k| ≤ 1)
    (cert : PolyAbstractionError sys.f A B xs us pZ Ba (construct U) L hp W) :
    sys.LinStep (S := 𝒫𝒵) U :=
  ⟨A, B, xs, us, pZ.subsetAt Ba, L ⊞ W, AbstractionError.of_poly hBa cert⟩

/-- The re-linearization loop at those steps, verbatim: the same theorem, the
same hypotheses, a non-convex representation underneath. -/
example {n m : ℕ} (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : PolyZonotope (Vec ℝ n))
    (U : PolyZonotope (Vec ℝ m)) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m)
    (steps : ℕ → sys.LinStep (S := 𝒫𝒵) U) (Ud : ℕ → PolyZonotope (Vec ℝ n)) (Δt : ℝ) (N : ℕ)
    (traj : sys.Trajectory (S := 𝒫𝒵) T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt), x t ∈ (steps i).R)
    (hU : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hUd : ∀ i < N, (NonlinearSys.linearize (steps i).A).stepInput
      (fun t => sys.f (x t) (u t) - (steps i).A *ᵥ x t) Δt i ∈ construct (Ud i))
    {o : ℕ} (ho : 0 < o) :
    ∀ i ≤ N, x ((i : ℝ) * Δt) ∈ construct (sys.relinReach o ho Δt steps Ud R₀ i) :=
  traj.relinReach_outer hΔt hT hR hU hUd ho

/-- A search the certificate accepts hands back a `LinStep`, ready for
`relinReach_outer` exactly as one built by hand. -/
noncomputable example {n m : ℕ} (sys : NonlinearSys n m) (U : PolyZonotope (Vec ℝ m))
    (A : Mat ℝ n n) (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m) (pZ L : PolyZonotope (Vec ℝ n))
    (Ba : Set (Fin pZ.p → ℝ)) (hp : L.p = pZ.p) (hBa : ∀ a ∈ Ba, ∀ k, |a k| ≤ 1)
    (Ws : ℕ → PolyZonotope (Vec ℝ n)) (fuel : ℕ)
    (h : (sys.abstrErrPolySearch U A B xs us pZ Ba L hp hBa Ws fuel).isSome) :
    sys.LinStep (S := 𝒫𝒵) U :=
  (sys.abstrErrPolySearch U A B xs us pZ Ba L hp hBa Ws fuel).get h

end CORALean.Real
