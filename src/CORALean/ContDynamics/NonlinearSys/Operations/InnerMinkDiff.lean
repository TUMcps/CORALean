module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffLoop

@[expose] public section

/-!
# `innerMinkDiff`, the inner Minkowski-difference algorithm

[1, Alg. 1]: from the initial set `X₀`, `ω` steps of size `Δt = t_end/ω` with enlargement factor
`μ = 1.1` (line 1), each step linearizing at `cen(R̂(t_k)) + ½Δt f(·)`, bounding the Lagrange
remainder until `L ⊆ L̂`, and computing `R̂(t_{k+1})` by `Prop. 1` and `R̂(τ_k)` by `Prop. 2`
(lines 2-17, `innerMinkDiffLoop`); the output is line 18's union `R̂(τ) = ⋃_k R̂(τ_k)`, an inner
approximation of the reachable set. `fuel` bounds each step's remainder loop; `none` when one
runs out. The listing requires a polytopic `X₀` and the autonomous field `f`.

## Inputs
* `ops` – set operations
* `f` – autonomous field
* `X₀` – initial set
* `tend` – final time
* `ω` – number of steps
* `fuel` – bound per remainder loop

## Output
* the inner approximation over the whole time, or none

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the inner approximation `R̂(τ)` of the reachable set over `[0, t_end]`. -/
noncomputable def NonlinearSys.innerMinkDiff (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (f : Vec ℝ n → Vec ℝ n) (X₀ : Set (Vec ℝ n)) (tend : ℝ) (ω fuel : ℕ) :
    Option (Set (Vec ℝ n)) :=
  -- 1. Δt ← t_end/ω
  let Δt := tend / ω
  -- 1. R̂(t₀) ← X₀
  let Rt0 := X₀
  -- 1. μ ← 1.1
  let μ : ℝ := 11 / 10
  -- 2. lines 2-18: R̂(τ)
  (NonlinearSys.innerMinkDiffLoop ops f Δt μ fuel ω Rt0 ∅).map Prod.snd

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
