module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# `reachBox`: [1, Alg. 2], the wrapping-free reachable set with `box()`

[1, Alg. 2], "Compute `R([0, t_f])`", for `ẋ = Ax + u`, `u ∈ U ∋ 0`, on zonotopes, one `let`
per printed line: `H^R_0 = CH(X⁰, e^{Ar}X⁰) + F X⁰` (`timeIntervalStep`),
`V₀ = ⊕ᵢ Aⁱrⁱ⁺¹/(i+1)! U ⊕ E(r)·r·U` (`inputSolution`, [1, Thm. 3.1]), `P^R_0 = box(V₀)`,
`R₀ = H^R_0 + P^R_0`, and then, `N` times, `H^R_k = e^{Ar}H^R_{k-1}`, `V_k = e^{Ar}V_{k-1}`,
`P^R_k = P^R_{k-1} + box(V_k)` and `R_k = H^R_k + P^R_k`. The result is the list
`R₀, …, R_N`, whose union is the printed `R([0, t_f])` at `N = t_f/r - 1`.

`box` is `Zonotope.interval` read back as a zonotope, which keeps the order of `P^R_k` at
one: the point of the listing, the input part's generators not piling up. The step is the
exact `e^{Ar}`. `LinearSys.WithInput.reach` runs the same windows without `box()`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: `R₀, …, R_N`, `R_k ⊇ R([kr, (k+1)r])`, from `X⁰` and `U` at Taylor order `η`. -/
noncomputable def LinearSys.reachBox (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n)) (r : ℝ)
    (η N : ℕ) : List (Zonotope (Vec ℝ n)) :=
  let eAr := exp (r • toRealMat sys.A)                             -- e^{Ar}
  -- 1. H^R_0 = CH(X⁰, e^{Ar}X⁰) + F X⁰
  let H₀ := sys.timeIntervalStep (S := 𝒵) r η X₀
  -- 2. V₀ = ⊕ Aⁱrⁱ⁺¹/(i+1)! U ⊕ E(r)·r·U
  let V₀ := sys.inputSolution (S := 𝒵) r η U
  -- 3. P^R_0 = box(V₀)
  let P₀ := V₀.interval.zonotope
  -- 4. R₀ = H^R_0 + P^R_0
  let R₀ := H₀.plus P₀
  -- 5. for k = 1 … (t_f/r - 1)
  ((List.range N).foldl
    (fun (s : (Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n))
        × List (Zonotope (Vec ℝ n))) _ =>
      -- 6. H^R_k = e^{Ar} H^R_{k-1}
      let Hₖ := s.1.1.mtimes eAr
      -- 7. V_k = e^{Ar} V_{k-1}
      let Vₖ := s.1.2.1.mtimes eAr
      -- 8. P^R_k = P^R_{k-1} + box(V_k)
      let Pₖ := s.1.2.2.plus Vₖ.interval.zonotope
      -- 9. R_k = H^R_k + P^R_k
      let Rₖ := Hₖ.plus Pₖ
      ((Hₖ, Vₖ, Pₖ), s.2 ++ [Rₖ]))
    ((H₀, V₀, P₀), [R₀])).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
