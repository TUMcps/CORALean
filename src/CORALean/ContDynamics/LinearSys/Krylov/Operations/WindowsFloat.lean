module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.SubspaceFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The time-interval sets of a Krylov subspace, in floats

[1, Alg. 2] for one vector, in the form CORA's `priv_reach_krylov` runs it: the vector lives in
its subspace, `e^{tA}c ≈ ν V e^{tT}e₁`, so the time-point and time-interval sets of the
`k`-dimensional system `ẏ = T y` from `y(0) = e₁` are those of `LinearSys.reachFloat`, window by
window, with the curvature `[F]` applied to the set at the start of the window, as
`Alg2Corrected` does and CORA's `aux_propagate_HomSol` does not (it applies `F e₁` to the matrix
at the end of the step). The window of `x(t)` is `ν V` of the small window, plus a ball of the
subspace error. The first Krylov column is `e₁`; sets of the state space are never formed here.

## Inputs
* `r` – the Krylov subspace
* `Δt` – time step
* `tFinal` – final time
* `η` – Taylor terms
* `ρ` – zonotope order

## Output
* the windows and the time-point sets of the `k`-dimensional system, if the run completes

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The system `ẏ = T y` of the subspace, `T` the stored Hessenberg matrix. -/
@[step_of Krylov.windowsFloat]
def Krylov.step_subspaceSys (r : Krylov.SubspaceFloat 𝕋 n) : LinearSys 𝕋 r.order :=
  { m := 0, q := 0, r := 0, s := 0, A := fun i j => r.H i j, B := fun _ j => j.elim0,
    c := fun _ => zero, C := fun i => i.elim0, D := fun i => i.elim0, k := fun i => i.elim0,
    E := fun _ j => j.elim0, F := fun i => i.elim0 }


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows and time points of `ẏ = T y`, `y(0) = e₁`, over `[0, tFinal]`. -/
def Krylov.windowsFloat (r : Krylov.SubspaceFloat 𝕋 n) (Δt : 𝕋) (tFinal : ℚ) (η ρ : ℕ) :
    Option (List (Zonotope (Vec 𝕋 r.order)) × List (Zonotope (Vec 𝕋 r.order))) :=
  (Krylov.step_subspaceSys r).reachFloat
    { X₀ := Zonotope.point fun i : Fin r.order => if i.val = 0 then one else zero,
      tFinal := tFinal }
    { Δt := Δt, η := η, ρ := ρ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
