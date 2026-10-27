module

public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# `reachBox`: [1, Alg. 1], the wrapping-free reachable set with `box()`

[1, Alg. 1], "Compute `R_k := R([t_k, t_{k+1}])` for `k = 1 … N`", for `ẋ = Ax + u`, `u ∈ U ∋ 0`, on
zonotopes, one `let` per printed line, its inputs `R^h_0`, `R^i_0` computed first:
`H^R_0 = CH(X⁰, e^{Ar}X⁰) + F X⁰` (`timeInterval`, [2, Sec. V-B]) and
`V₀ = ⊕ᵢ Aⁱrⁱ⁺¹/(i+1)! U ⊕ E(r)·r·U` (`inputSolution`, [2, Prop. 2] in its corrected form). Then
`P^R_0 = box(V₀)`, `R₀ = H^R_0 + P^R_0`, and `N` times `H^R_k = e^{Ar}H^R_{k-1}`,
`V_k = e^{Ar}V_{k-1}`, `P^R_k = P^R_{k-1} + box(V_k)` and `R_k = H^R_k + P^R_k`. The result is the
list `R₀, …, R_N`, [1]'s output. `box` is `Zonotope.interval` read back as a zonotope, so `P^R_k`
keeps order one. The step is the exact `e^{Ar}`; `WithInput.reach` drops `box()`.

## Inputs
* `sys` – linear system
* `X₀` – initial zonotope
* `U` – input zonotope
* `r` – step length
* `η` – Taylor order
* `N` – number of steps

## Output
* reachable zonotopes of the steps

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
* [2] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
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

/-- [1, Alg. 1]: `R₀, …, R_N`, `R_k ⊇ R([kr, (k+1)r])`, from `X⁰` and `U` at Taylor order `η`. -/
noncomputable def LinearSys.reachBox (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n)) (r : ℝ)
    (η N : ℕ) : List (Zonotope (Vec ℝ n)) :=
  let eAr := exp (r • toRealMat sys.A)                             -- e^{Ar}
  -- 1. H^R_0 = CH(X⁰, e^{Ar}X⁰) + F X⁰
  let H₀ := sys.timeInterval (S := 𝒵) r η X₀
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
