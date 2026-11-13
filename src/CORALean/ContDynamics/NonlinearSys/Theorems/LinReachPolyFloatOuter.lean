module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachPolyLoopFloatOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsNominal
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceSplitOuter

@[expose] public section

/-!
# One step of CORA's `linReach` from a polynomial zonotope, reduced, holds every run

`linReachPolyLoopFloat_outer` followed by `post`'s reduction. `reduceCora` chooses the generators
to remove and hands them to `reduceSplit`, which encloses for every choice; at or below the count
it only drops the unused factors, which encloses. So the reduced sets hold what the sets did.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the error
* `fuel` – iteration bound
* `R` – start polynomial zonotope
* `abstrerr` – the last step's abstraction error
* `maxError` – largest admissible error, if any
* `order` – the order of equal exponent columns

## Hypotheses
* `h` – model encloses system

## Conclusion
* a successful step encloses every run over the step and at its end, after the reduction
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- The polynomial zonotope lies in its reduction. -/
private theorem aux_reduceCora_outer (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ)
    (order : ℕ → Array (Array ℕ) → Array ℕ) :
    pZ.toSet ⊆ (pZ.reduceCora o order).1.toSet := by
  unfold PolyZonotope.reduceCora
  split_ifs
  · exact PolyZonotope.reduceSplit_outer _ _ _ _ _ _
  · exact PolyZonotope.compactFactors_outer pZ


-- =======================================  MAIN THEOREM  ======================================= --

/-- After `post`'s reduction the sets still hold every run. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachPolyFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋} {fuel : ℕ}
    {R : PolyZonotope (Vec 𝕋 n)} {abstrerr : Vec 𝕋 n} {maxError : Option (Vec 𝕋 n)}
    {order : ℕ → Array (Array ℕ) → Array ℕ} : -- --- CONCL ---
    ∀ S Rτ Rt, (S, Rτ, Rt) ∈ fm.linReachPolyFloat U options enlarge fuel R abstrerr
        maxError order →
      0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U.toSet x u y →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.1.toSet) ∧
          x (toReal options.Δt) ∈ Rt.1.toSet := by -- --- PROOF ---
  intro S Rτ Rt (hP : fm.linReachPolyFloat U options enlarge fuel R abstrerr maxError order
    = some (S, Rτ, Rt))
  unfold NonlinearSys.FloatHessModel.linReachPolyFloat at hP
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hP
  obtain ⟨S', hS, hpure⟩ := hP
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl, rfl⟩ := hpure
  obtain ⟨hΔt, hout⟩ := h.linReachPolyLoopFloat_outer _ _ _ hS
  refine ⟨hΔt, fun {x u y} traj => ?_⟩
  obtain ⟨h1, h2⟩ := hout traj
  exact ⟨fun t ht => aux_reduceCora_outer _ _ _ (h1 t ht),
    aux_reduceCora_outer _ _ _ h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
