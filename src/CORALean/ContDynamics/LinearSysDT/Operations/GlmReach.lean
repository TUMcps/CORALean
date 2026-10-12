import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# `glmReach`: [1, Alg. 1], the recurrence `Ω_{i+1} = ΦΩᵢ ⊕ U` without the wrapping effect

[1, Alg. 1] on zonotopes, one `let` per printed line: `X₀ = Ω₀`, `V₀ = U`, `S₀ = {0}`,
and then, `N` times, `X_{i+1} = ΦXᵢ`, `S_{i+1} = Sᵢ ⊕ Vᵢ`, `V_{i+1} = ΦVᵢ` and
`Ω_{i+1} = X_{i+1} ⊕ S_{i+1}`. The result is the list `Ω₁, …, Ω_N`. The linear map is
only ever applied to `Xᵢ` and `Vᵢ`, whose generator counts stay those of `Ω₀` and `U`;
`Sᵢ` grows by concatenation alone. `Φ` is the state matrix of the discrete-time system.
Its exactness, the paper's output line, is `LinearSysDT.glmReach_eq`.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: `Ω₁, …, Ω_N` of `Ω_{i+1} = ΦΩᵢ ⊕ U`, as `Ω_{i+1} = X_{i+1} ⊕ S_{i+1}`. -/
def LinearSysDT.glmReach (sys : LinearSysDT 𝕋 n) (Ω₀ U : Zonotope (Vec ℝ n))
    (N : ℕ) : List (Zonotope (Vec ℝ n)) :=
  let Φ := toRealMat sys.A                                          -- the matrix Φ
  let X₀ := Ω₀                                                      -- 1: X₀ ← Ω₀
  let V₀ := U                                                       -- 2: V₀ ← U
  let S₀ := Zonotope.ofPoint (0 : Vec ℝ n)                          -- 3: S₀ ← {0}
  ((List.range N).foldl                                             -- 4: for i from 0 to N - 1
    (fun (s : (Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n))
        × List (Zonotope (Vec ℝ n))) _ =>
      let X' := s.1.1.mtimes Φ                                      -- 5: X_{i+1} ← ΦXᵢ
      let S' := s.1.2.1.plus s.1.2.2                                -- 6: S_{i+1} ← Sᵢ ⊕ Vᵢ
      let V' := s.1.2.2.mtimes Φ                                    -- 7: V_{i+1} ← ΦVᵢ
      let Ω' := X'.plus S'                                     -- 8: Ω_{i+1} ← X_{i+1} ⊕ S_{i+1}
      ((X', S', V'), s.2 ++ [Ω']))
    ((X₀, S₀, V₀), [])).2                                           -- 10: return {Ω₁, …, Ω_N}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
