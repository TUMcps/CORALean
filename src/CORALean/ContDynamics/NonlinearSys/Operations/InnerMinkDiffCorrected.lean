module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffCorrectedLoop

@[expose] public section

/-!
# `innerMinkDiffCorrected`, the inner Minkowski-difference algorithm with lines 15-16 repaired

[1, Alg. 1]: from the initial set `X₀`, `ω` steps of size `Δt = t_end/ω` with enlargement factor
`μ = 1.1` (line 1), each step linearizing at `cen(R̂(t_k)) + ½Δt f(·)`, bounding the Lagrange
remainder until `L ⊆ L̂`, and computing `R̂(t_{k+1})` by `Prop. 1` and `R̂(τ_k)` by `Prop. 2`
(lines 2-17, `innerMinkDiffCorrectedLoop`); the output is line 18's union `R̂(τ) = ⋃_k R̂(τ_k)`.
Lines 15 and 16 are repaired as in `innerMinkDiffCorrectedStep`: `Prop. 1`'s shift, and the hull
eroded by the ball `B_µ` of [2], `µ` from the generators `zono` gives `R̂(t_k)`. `fuel` bounds
each step's remainder loop; `none` when one runs out. The listing requires a polytopic `X₀` and
the autonomous field `f`.

## Inputs
* `ops` – set operations
* `zono` – zonotope of a set's center and generators
* `f` – autonomous field
* `X₀` – initial set
* `tend` – final time
* `ω` – number of steps
* `fuel` – bound per remainder loop

## Output
* the inner approximation over the whole time, or none

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
* [2] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] with lines 15-16 repaired: the inner approximation `R̂(τ)` over `[0, t_end]`. -/
noncomputable def NonlinearSys.innerMinkDiffCorrected (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n)) (f : Vec ℝ n → Vec ℝ n)
    (X₀ : Set (Vec ℝ n)) (tend : ℝ) (ω fuel : ℕ) :
    Option (Set (Vec ℝ n)) :=
  -- 1. Δt ← t_end/ω
  let Δt := tend / ω
  -- 1. R̂(t₀) ← X₀
  let Rt0 := X₀
  -- 1. μ ← 1.1
  let μ : ℝ := 11 / 10
  -- 2. lines 2-18: R̂(τ)
  (NonlinearSys.innerMinkDiffCorrectedLoop ops zono f Δt μ fuel ω Rt0 ∅).map Prod.snd

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
