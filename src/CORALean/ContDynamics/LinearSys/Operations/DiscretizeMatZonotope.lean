module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosure
public import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

@[expose] public section

/-!
# Sampling a continuous-time system, the exponential enclosed by a matrix zonotope

`discretizeEnclosure` again, at a matrix zonotope in place of an interval
matrix. Not a second spelling of the same thing: an interval matrix throws away
every correlation between the entries of `e^{AΔt}`, a matrix zonotope keeps
them, and that is why CORA carries `matZonotope` alongside `intervalMatrix`
[1, Sec. 3.3.2].

`sys.A` is one fixed matrix, so `ofPoint` is what enters the enclosure; the
width is entirely the exponential's truncation error, and it leaves the
enclosure as generators rather than as a box, so what multiplies a reachable
set is a zonotope rather than an interval matrix.

`𝕄𝒵` names this family, but only `Zonotope/Real/Instances` declares it, and
that file brings the instances a *use* wants and a definition does not — so the
family is written out here, as `discretizeEnclosure` writes out `ℐ`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar
open scoped CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind, its matrix enclosed by a matrix
zonotope: the Taylor truncation at order `η` widened by the tail bound. -/
noncomputable def LinearSys.discretizeMatZonotope (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) :
    LinParamSysDT 𝕄𝒵 n :=
  ⟨Real.MatExp.expMatZonoEnclosure (Real.Zonotope.ofPoint (Δt • toRealMat sys.A)) η⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
