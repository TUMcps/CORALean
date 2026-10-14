module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

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

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: `Ω₁, …, Ω_N` of `Ω_{i+1} = ΦΩᵢ ⊕ U`, as `Ω_{i+1} = X_{i+1} ⊕ S_{i+1}`. -/
def LinearSysDT.glmReach (sys : LinearSysDT 𝕋 n) (Ω₀ U : Zonotope (Vec ℝ n))
    (N : ℕ) : List (Zonotope (Vec ℝ n)) :=
  -- the matrix `Φ`
  let Φ := toRealMat sys.A
  -- 1. X₀ ← Ω₀
  let X₀ := Ω₀
  -- 2. V₀ ← U
  let V₀ := U
  -- 3. S₀ ← {0}
  let S₀ := Zonotope.ofPoint (0 : Vec ℝ n)
  -- 4. for i from 0 to N - 1
  ((List.range N).foldl
    (fun (s : (Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n))
        × List (Zonotope (Vec ℝ n))) _ =>
      -- 5. X_{i+1} ← ΦXᵢ
      let X' := s.1.1.mtimes Φ
      -- 6. S_{i+1} ← Sᵢ ⊕ Vᵢ
      let S' := s.1.2.1.plus s.1.2.2
      -- 7. V_{i+1} ← ΦVᵢ
      let V' := s.1.2.2.mtimes Φ
      -- 8. Ω_{i+1} ← X_{i+1} ⊕ S_{i+1}
      let Ω' := X'.plus S'
      ((X', S', V'), s.2 ++ [Ω']))
    -- 10. return {Ω₁, …, Ω_N}
    ((X₀, S₀, V₀), [])).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
