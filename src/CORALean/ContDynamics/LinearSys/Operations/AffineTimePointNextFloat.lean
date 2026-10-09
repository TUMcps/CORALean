import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# `H(t_{k+1})` from `H(t_k)`, in floats

`MatExp.affineTimePointNext` computed in `𝕋`: [1, Alg. 1] lines 6-7's
`H(t_{k+1}) = e^{AΔt}H(t_k) ⊕ A^{-1}(e^{AΔt}-I_n)ũ`, the exponential the float
`[e^{AΔt}]` and the constant's share `∫₀^Δt e^{Aσ}dσ ũ` the float input solution of the point
`{ũ}`, which holds it at an admissible order.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
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

/-- `[e^{AΔt}] H ⊕ P^u(Δt)`, `P^u(Δt)` the float input solution of `{ũ}` at order `η`. -/
def LinearSys.affineTimePointNextFloat (sys : LinearSys 𝕋 n) (H : Zonotope 𝕋 n) (ũ : Vec 𝕋 n)
    (Δt : 𝕋) (η : ℕ) : Zonotope 𝕋 n :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                          -- [e^{AΔt}]
  let PuΔt := sys.inputSolutionFloat Δt η (Interval.point ũ).zonotope  -- ∋ A^{-1}(e^{AΔt}-I)ũ
  Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAΔt H ⊞ PuΔt  -- H(t_{k+1})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
