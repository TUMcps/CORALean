module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrectionMatrix
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.Map

@[expose] public section

/-!
# One step of the homogeneous flow at a matrix zonotope, as a set

`LinParamSys.timeInterval` at `𝕄𝒵`, CORA's `initReach` with `obj.A` a
`matZonotope`: `CH(X₀, e^{[A]r} X₀) ⊕ F X₀`, the exponential kept as a matrix
zonotope (`expMatZonoEnclosure` of `r • A`, the dependency between a member's own
powers preserved) and the correction matrix CORA's `priv_tie` builds, which boxes
the zonotope powers (`matZonoCorrectionMatrix`).

`r • A` is the image of `A` under scaling, `Zonotope.map`, as `expMatZonoTerm`
scales its powers.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `X₀` – initial set

## Output
* the set covering the flow over the step at a matrix zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes 𝕄𝒵 S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `CH(X₀, e^{Ar}X₀) ⊕ F X₀` with `A` ranging over a matrix zonotope. -/
noncomputable def LinParamSys.timeIntervalZono (sys : LinParamSys 𝕄𝒵 n) (r : ℝ) (η : ℕ)
    (X₀ : S n) : S n :=
  let Ar := Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) r) sys.A      -- A * stepSize
  let eAr := MatExp.expMatZonoEnclosure Ar η                          -- mappingMatrixSet
  let F := MatExp.matZonoCorrectionMatrix sys.A r η                    -- priv_tie's F
  LinComb.linComb X₀ (Mtimes.mtimes (𝕄 := 𝕄𝒵) eAr X₀) ⊞ Mtimes.mtimes (𝕄 := ℐ) F X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
