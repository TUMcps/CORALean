module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpEnclosure
public import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

@[expose] public section

/-!
# Sampling a continuous-time system, the exponential only enclosed

`discretize` puts `e^{AΔt}` into a `LinearSysDT` as an exact real matrix, but
`e^{AΔt}` is transcendental — nothing can compute it. `expEnclosure` is the
computable enclosure of it, and an enclosure is a *set* of matrices, so the
discretized system is no longer a `LinearSysDT` at all: it is a `LinParamSysDT`
over interval matrices. The uncertainty here is not modelling uncertainty, it
is the numerical error of the exponential, and `LinParamSysDT` is exactly its
home.

`ℐ` (`ContSet/Interval/Real/Instances`) would name the matrix family, but it
comes with the `ConvexSet`/`CompactSet`/`Mtimes` instances a *use* of this
system wants and a mere definition does not, so the family is written out here.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind, its matrix only enclosed: the
Taylor truncation at order `η` widened by the tail bound, [1, Sec. 3.2]. -/
noncomputable def LinearSys.discretizeEnclosure (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) :
    LinParamSysDT (fun m n => Real.Interval (Mat ℝ m n)) n :=
  ⟨Real.MatExp.expEnclosure (Δt • toRealMat sys.A) η⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
