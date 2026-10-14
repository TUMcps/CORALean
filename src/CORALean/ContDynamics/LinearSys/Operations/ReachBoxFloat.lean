module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `reachBoxFloat`: [1, Alg. 2], the wrapping-free reachable set with `box()`, in floats

`reachBox` computed in `𝕋`, one `let` per printed line: `H^R_0 = CH(X⁰, e^{Ar}X⁰) + F X⁰`
(`timeIntervalStepFloat`), `V₀ = ⊕ᵢ Aⁱrⁱ⁺¹/(i+1)! U ⊕ E(r)·r·U` (`inputSolutionFloat`),
`P^R_0 = box(V₀)`, `R₀ = H^R_0 + P^R_0`, and then, `N` times, `H^R_k = [e^{Ar}]H^R_{k-1}`,
`V_k = [e^{Ar}]V_{k-1}`, `P^R_k = P^R_{k-1} + box(V_k)` and `R_k = H^R_k + P^R_k`.

The step `e^{Ar}` is the float interval matrix `expIntervalFloat r r η` and a product with it
is `Zonotope.mtimesIntervalMat`, which encloses; the next product starts from that enclosure,
so the rounding compounds with `k`, as `reachBox`'s exact `e^{Ar}` does not. `box` is
`Zonotope.interval` read back as a zonotope, rounded outward. `η` is raised with
`reachOrderFloat` to the first order the float remainder bound at `r · A` admits; `none` when
that search fails. The result is the list `R₀, …, R_N`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] in floats: `R₀, …, R_N`, `R_k ⊇ R([kr, (k+1)r])`, from `X⁰` and `U` at Taylor
order `η` raised until admissible. -/
def LinearSys.reachBoxFloat (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec 𝕋 n)) (r : 𝕋) (η N : ℕ) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  let η' ← sys.reachOrderFloat r r η                               -- η, raised until admissible
  let eAr := sys.expIntervalFloat r r η'                           -- [e^{Ar}]
  -- 1. H^R_0 = CH(X⁰, e^{Ar}X⁰) + FX⁰
  let H₀ := sys.timeIntervalStepFloat r η' X₀
  -- 2. V₀ = ⊕ Aⁱrⁱ⁺¹/(i+1)! U ⊕ E·r·U
  let V₀ := sys.inputSolutionFloat r η' U
  -- 3. P^R_0 = box(V₀)
  let P₀ := V₀.interval.zonotope
  -- 4. R₀ = H^R_0 + P^R_0
  let R₀ := H₀ ⊞ P₀
  let ℰ := fun (Z : Zonotope (Vec 𝕋 n)) =>                               -- Z ↦ [e^{Ar}] Z
    Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eAr Z
  -- 5. for k = 1 … (t_f/r - 1)
  pure ((List.range N).foldl
    (fun (s : (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) × List
      (Zonotope (Vec 𝕋 n))) _ =>
      -- 6. H^R_k = e^{Ar} H^R_{k-1}
      let Hₖ := ℰ s.1.1
      -- 7. V_k = e^{Ar} V_{k-1}
      let Vₖ := ℰ s.1.2.1
      -- 8. P^R_k = P^R_{k-1} + box(V_k)
      let Pₖ := s.1.2.2 ⊞ Vₖ.interval.zonotope
      -- 9. R_k = H^R_k + P^R_k
      let Rₖ := Hₖ ⊞ Pₖ
      ((Hₖ, Vₖ, Pₖ), s.2 ++ [Rₖ]))
    ((H₀, V₀, P₀), [R₀])).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
