module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `glmReachBox`: [1, Alg. 2], the interval hulls of `Ω₁, …, Ω_N`

[1, Alg. 2] on zonotopes and interval products, one `let` per printed line: `X₀ = Ω₀`,
`V₀ = U`, `S₀ = {0}`, and then, `N` times, `X_{i+1} = ΦXᵢ`, `S_{i+1} = Sᵢ ⊕ Box(Vᵢ)`,
`V_{i+1} = ΦVᵢ` and `Ω̄_{i+1} = Box(X_{i+1}) ⊕ S_{i+1}`. `Xᵢ` and `Vᵢ` are zonotopes, `Sᵢ`
and `Ω̄ᵢ` interval products, `Box` of a zonotope is `Zonotope.interval`, its centre plus and
minus the sums of the generators' absolute entries. The box is only ever taken of an
exact set, so nothing compounds: [1, Prop. 1], `LinearSysDT.glmReachBox_eq_hull`, says
`Ω̄ᵢ` is the interval hull of `Ωᵢ`.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: `Ω̄₁, …, Ω̄_N`, `Ω̄_{i+1} = Box(X_{i+1}) ⊕ S_{i+1}`. -/
def LinearSysDT.glmReachBox (sys : LinearSysDT 𝕋 n) (Ω₀ U : Zonotope (Vec ℝ n))
    (N : ℕ) : List (Interval (Vec ℝ n)) :=
  let Φ := toRealMat sys.A                                          -- the matrix Φ
  let X₀ := Ω₀                                                      -- 1: X₀ ← Ω₀
  let V₀ := U                                                       -- 2: V₀ ← U
  let S₀ : Interval (Vec ℝ n) := ⟨0, 0⟩                             -- 3: S₀ ← {0}
  ((List.range N).foldl                                             -- 4: for i from 0 to N - 1
    (fun (s : (Zonotope (Vec ℝ n) × Interval (Vec ℝ n) × Zonotope (Vec ℝ n))
        × List (Interval (Vec ℝ n))) _ =>
      let X' := s.1.1.mtimes Φ                                      -- 5: X_{i+1} ← ΦXᵢ
      let S' := s.1.2.1.plus s.1.2.2.interval                       -- 6: S_{i+1} ← Sᵢ ⊕ Box(Vᵢ)
      let V' := s.1.2.2.mtimes Φ                                    -- 7: V_{i+1} ← ΦVᵢ
      let Ω' := X'.interval.plus S'                     -- 8: Ω̄_{i+1} ← Box(X_{i+1}) ⊕ S_{i+1}
      ((X', S', V'), s.2 ++ [Ω']))
    ((X₀, S₀, V₀), [])).2                                           -- 10: return {Ω̄₁, …, Ω̄_N}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
