import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagateFloat
import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolutionFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat

/-!
# One window with the input set split, at every member, in floats

`LinParamSys.WithInputSplit.reachStepk` computed in `𝕋`, `U = ũ ⊕ Ũ` [1, Alg. 4]:
`R(τ_k) = [e^{[A]t_k}](H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R_Ũ(t_{k+1})`. The first
window's set `Rτ₀ = (H^R ⊕ P̃^R)(τ_0)` is taken, as `reachStepkFloat` takes `H^R(τ_0)`,
so no window pays for it again.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` from the first one `Rτ₀`, `U = ũ ⊕ Ũ`, at
every member of `sys.A`. -/
def LinParamSys.reachStepkFloatInputSplit
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) (U : Zonotope 𝕋 n) (ρ : ℕ)
    (Δt : 𝕋) (η : ℕ) (Rτ₀ : Zonotope 𝕋 n) (k : ℕ) : Option (Zonotope 𝕋 n) := do
  let uc := ScalarCentre.centreVec (S := Zonotope 𝕋) U           -- ũ, the constant
  let U₀ := Recentre.recentre U                                    -- Ũ = U - ũ, holding 0
  let Hτk ← sys.reachStepkFloat Δt η Rτ₀ k                         -- [e^{[A]t_k}](H^R ⊕ P̃^R)(τ_0)
  let Pctk := sys.constPropagateFloat Δt η ρ uc k                  -- P̃(t_k)
  let PRtk ← sys.particularSolutionFloat Δt η ρ U₀ k               -- P^R_Ũ(t_{k+1})
  pure ((Hτk ⊞ Pctk) ⊞ PRtk)                                       -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
