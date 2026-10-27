module

public import CORALean.ContDynamics.LinearSys.Operations.ManualRun
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `manualRun`'s `H` is exact, not an enclosure

[1, Alg. 1] treats `H(t_k)` as an exact set throughout: Line 7's
`H(t_{k+1}) ← e^{At_{k+1}}X₀ + P^u(t_{k+1})` names no enclosure, unlike `Ĥ(τ_k)` and `R̂(τ_k)`,
which do. This is that reading, made outright: `manualRun`'s `H` field always denotes the image of
`X₀` under `e^{A t_k}`, Minkowski-shifted by the exact particular solution `P^u(t_k)`.
`Zonotope.mtimes_exact` and `Zonotope.plus_exact` make the `⊆` of `mtimes_outer`/`plus_outer`
equalities. This does *not* establish `H(t_k) ⊇ R(t_k)` against [1]'s `Def. 6`: that needs the
particular solution due to the *uncertain* part `U₀` of the input, which `P̂^U(t_k)` answers for.

## Inputs
* `sys` – linear system
* `X₀` – initial zonotope
* `U` – input zonotope
* `Δt` – step length
* `η` – Taylor order
* `ρ` – zonotope order
* `k` – step index

## Hypotheses
* none

## Conclusion
* the state's H is exactly the propagated start set shifted by the particular solution

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Pointwise Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Zonotope.ofPoint v`'s own set, read off `mem_ofPoint_iff` rather than membership alone. -/
private theorem aux_construct_ofPoint {α : Type} [AddCommGroup α] [Module ℝ α] (v : α) :
    (Zonotope.ofPoint v).construct = {v} :=
  Set.ext fun x => (Zonotope.mem_ofPoint_iff v x).trans Set.mem_singleton_iff.symm


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] line 7, made exact: the state `manualRun` reaches at step `k` has `H` denoting
precisely `e^{A t_k}·X₀`, Minkowski-shifted by `P^u(t_k)`. -/
theorem LinearSys.manualRun_H_exact (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n)) (Δt : ℝ)
    (η ρ : ℕ) (k : ℕ) : -- --- CONCL ---
    construct (sys.manualRun X₀ U Δt η ρ k).H
      = (fun x₀ => exp ((sys.manualRun X₀ U Δt η ρ k).t • toRealMat sys.A) *ᵥ x₀)
          '' construct X₀ + {(sys.manualRun X₀ U Δt η ρ k).Pu} := by -- --- PROOF ---
  cases k with
  | zero =>
    simp only [LinearSys.manualRun, LinearSys.step_manualInit]
    have hexp0 : exp ((0:ℝ) • toRealMat sys.A) = 1 := by simp
    rw [hexp0]
    ext x
    simp
  | succ k =>
    simp only [LinearSys.manualRun, LinearSys.manualStep]
    show Zonotope.construct _ = _
    rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact, aux_construct_ofPoint]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
