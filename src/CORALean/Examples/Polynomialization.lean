import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfPoly
import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachPolyOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinDeltaReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter
import CORALean.ContSet.Conversion.Real.Instances
import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# The polynomialization variant runs the loop already proved

Step three of CORA's `alg = 'poly'`, lines 4-18 of [1, Alg. 1], is not a second induction. A
`IsPolyAbstractionError` becomes a `LinStep` through `IsAbstractionError.of_poly`, and
`relinReach_outer` applies at `𝒫𝒵` with nothing added: soundness was stated at an arbitrary
certificate rather than at the one `alg = 'lin'` computes. The instances it takes are `Plus`,
`Reduce`, `Mtimes (Mat ℝ)`, `OfInterval`, `LinComb` and `Mtimes ℐ`, all of which `PolyZonotope`
has. `relinDeltaReach_outer` is CORA's `Rdiff`; the poly certificate confines the run to `subsetAt`
rather than a box. `linReachPoly` runs `abstrErrPolySearch`, `linReach`'s while loop, from a
system's derivatives and a start set.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open Matrix ContSet Plus

-- Anonymous, since their content is that they elaborate.

/-- A certificate over the factors is one linearization step of the loop. -/
example {n m : ℕ} (sys : NonlinearSys n m) (U : PolyZonotope (Vec ℝ m)) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m) (pZ L W : PolyZonotope (Vec ℝ n))
    (Ba : Set (Fin pZ.p → ℝ)) (hp : L.p = pZ.p) (hBa : ∀ a ∈ Ba, ∀ k, |a k| ≤ 1)
    (cert : IsPolyAbstractionError sys.f A B xs us pZ Ba (construct U) L hp W) :
    sys.LinStep (S := 𝒫𝒵) U :=
  ⟨A, B, xs, us, pZ.subsetAt Ba, L ⊞ W, IsAbstractionError.of_poly hBa cert⟩

/-- The re-linearization loop at those steps, verbatim: the same theorem, the
same hypotheses, a non-convex representation underneath. -/
example {n m : ℕ} (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : PolyZonotope (Vec ℝ n))
    (U : PolyZonotope (Vec ℝ m)) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m)
    (steps : ℕ → sys.LinStep (S := 𝒫𝒵) U) (Ud : ℕ → PolyZonotope (Vec ℝ n)) (Δt : ℝ) (N : ℕ)
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (S := 𝒫𝒵) T R₀ U x u y) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt), x t ∈ (steps i).R)
    (hU : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hUd : ∀ i < N, (NonlinearSys.linearize (steps i).A).stepInput
      (fun t => sys.f (x t) (u t) - (steps i).A *ᵥ x t) Δt i ∈ construct (Ud i))
    {o : ℕ} (ho : 0 < o) :
    ∀ i ≤ N, x ((i : ℝ) * Δt) ∈ construct (sys.relinReach ⟨R₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud) :=
  traj.relinReach_outer hΔt hT hR hU hUd ho

/-- A search the certificate accepts hands back a `LinStep`, ready for
`relinReach_outer` exactly as one built by hand. -/
noncomputable example {n m : ℕ} (sys : NonlinearSys n m) (U : PolyZonotope (Vec ℝ m))
    (A : Mat ℝ n n) (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m)
    (pZ L : ℕ → PolyZonotope (Vec ℝ n)) (Ba : ∀ k, Set (Fin (pZ k).p → ℝ))
    (hp : ∀ k, (L k).p = (pZ k).p) (hBa : ∀ k, ∀ a ∈ Ba k, ∀ j, |a j| ≤ 1)
    (Ws : ℕ → PolyZonotope (Vec ℝ n)) (fuel : ℕ)
    (h : (sys.abstrErrPolySearch U A B xs us pZ Ba L hp hBa Ws fuel).isSome) :
    sys.LinStep (S := 𝒫𝒵) U :=
  (sys.abstrErrPolySearch U A B xs us pZ Ba L hp hBa Ws fuel).get h

/-- CORA's `linReach` at `alg = 'poly'` on `ẋ = x² + u`, end to end: nothing but its
derivatives at `(xs, us)` — `A = 2xs`, `B = 1`, the Hessian `2` in the state block, no
third derivative — and the start set is handed in, no candidate error. -/
noncomputable example (U X₀ : PolyZonotope (Vec ℝ 1)) (xs us : Vec ℝ 1) :
    Option ((⟨fun x u i => x i ^ 2 + u i, 1, fun x _ => x⟩ : NonlinearSys 1 1).LinStep
      (S := 𝒫𝒵) U) :=
  (⟨fun x u i => x i ^ 2 + u i, 1, fun x _ => x⟩ : NonlinearSys 1 1).linReachPoly U
    (Matrix.of fun _ _ => 2 * xs 0) 1 xs us
    (fun _ => Matrix.of fun i j => if i = 0 ∧ j = 0 then 2 else 0) (fun _ _ => 0)
    (1 / 100) 4 50 50 X₀ 0 10

/-- Whatever step such a run returns, a trajectory confined to the region it
certified is inside the linearized reachable set at `Δt`. -/
example (sys : NonlinearSys 1 1) (U X₀ Ud : PolyZonotope (Vec ℝ 1)) (A : Mat ℝ 1 1)
    (xs us : Vec ℝ 1) (x : ℝ → Vec ℝ 1) (u : ℝ → Vec ℝ 1) (step : sys.LinStep (S := 𝒫𝒵) U)
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (S := 𝒫𝒵) (Set.Icc 0 (1 / 100)) X₀ U x u y)
    (h : sys.linReachPoly U A 1 xs us
      (fun _ => Matrix.of fun i j => if i = 0 ∧ j = 0 then 2 else 0) (fun _ _ => 0)
      (1 / 100) 4 50 50 X₀ 0 10 = some step)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 100), x t ∈ step.R)
    (hU : Bornology.IsBounded (construct step.linInput))
    (hUd : (NonlinearSys.linearize A).stepInput
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) (1 / 100) 0 ∈ construct Ud) :
    x (1 / 100) ∈ construct (((NonlinearSys.linearize A).discretize (1 / 100)).reach
      (S := 𝒫𝒵) ⟨X₀, Ud, 0, 1⟩ ⟨1, one_pos⟩) :=
  traj.linReachPoly_outer h subset_rfl hR (by norm_num) hU hUd one_pos

end CORALean.Real
