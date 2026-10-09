import CORALean.ContDynamics.LinearSys.Operations.AffineTimePointNextFloat
import CORALean.ContDynamics.LinearSys.Operations.AffineWindowFloat

/-!
# `comb(H(t_k), H(t_{k+1})) ⊕ C` in floats: eq. (22), line 9 of [1, Alg. 1]

[1]'s eq. (22), `Real.MatExp.affineTimeIntervalOuter`, computed in `𝕋`: `affineWindowFloat` at
`affineTimePointNextFloat`, `[e^{AΔt}] H ⊕ P^u(Δt)`, for `H(t_{k+1})`. A point of `H(t_k)`
flowing for any `τ ∈ [0, Δt]` is in it (`affineTimeIntervalOuterFloat_outer`).

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

/-- Eq. (22): `Ĥ(τ_k) = comb(H(t_k), H(t_{k+1})) ⊕ C`, with
`H(t_{k+1}) = [e^{AΔt}] H(t_k) ⊕ P^u(Δt)`. -/
def LinearSys.affineTimeIntervalOuterFloat (sys : LinearSys 𝕋 n) (H : Zonotope 𝕋 n)
    (ũ : Vec 𝕋 n) (Δt : 𝕋) (η : ℕ) : Zonotope 𝕋 n :=
  let Hnext := sys.affineTimePointNextFloat H ũ Δt η                  -- H(t_{k+1})
  sys.affineWindowFloat H Hnext ũ Δt η                                -- 9. comb(H, H') ⊕ C

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
