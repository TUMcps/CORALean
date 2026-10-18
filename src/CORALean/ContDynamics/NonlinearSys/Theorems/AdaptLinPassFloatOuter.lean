module

public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptLinPassFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.OneStepFloatOuter
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# The float linear pass holds the runs whose remainder stays in its input

`adaptLinPassFloat` is the linear pass of [1, Alg. 2] lines 3-6: the two sets of the linearization
alone, with the input `f(z✱) ⊕ B(U - u✱)` and no abstraction error. Its guarantee is the one of the
linear step it ends in (`oneStepFloat_outer`): a run of the nonlinear system whose field less its
linear part stays in that input is in the pass's sets. The abstraction error is what a step adds on
top (`adaptStepFloat_outer`). See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful pass has a positive width, and every run of `sys` on `[0, Δt]` from `R` under
inputs in `U` whose `f(x, u) - A(x - x✱)` stays in `f(z✱) ⊕ B(U - u✱)` is in `R_lin(τ_k)` over
the step and in `R_lin(t_{k+1})` at its end. -/
theorem NonlinearSys.FloatModel.adaptLinPassFloat_outer {fm : NonlinearSys.FloatModel 𝕋 n m}
    {sys : NonlinearSys n m} {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋}
    {R : Zonotope (Vec 𝕋 n)} : -- --- STMT ---
    ∀ A Rt Rτ, (A, Rt, Rτ) ∈ fm.adaptLinPassFloat U options R →
      0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
        sys.IsTrajectory (S := 𝒮) (Set.Icc 0 (toReal options.Δt))
          R.construct U.construct x u →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt),
          sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ
            (x t - toRealVec (fm.linPointFloat options.Δt R U).1) ∈
            ((fm.f (Interval.point (fm.linPointFloat options.Δt R U).1)
              (Interval.point (fm.linPointFloat options.Δt R U).2)).zonotope ⊞
              Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋])
                (fm.linearizeFloat (fm.linPointFloat options.Δt R U).1
                  (fm.linPointFloat options.Δt R U).2).2
                (Recenter.recenter U)).construct) →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.construct) ∧
          x (toReal options.Δt) ∈ Rt.construct := by -- --- PROOF ---
  intro A Rt Rτ (hpass : fm.adaptLinPassFloat U options R = some (A, Rt, Rτ))
  unfold NonlinearSys.FloatModel.adaptLinPassFloat at hpass
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hpass
  obtain ⟨S, hS, hpure⟩ := hpass
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl, rfl⟩ := hpure
  obtain ⟨hΔt, hout⟩ := NonlinearSys.oneStepFloat_outer (sys := sys) _ _ hS
  exact ⟨hΔt, fun traj => hout (U := U.construct) traj⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
