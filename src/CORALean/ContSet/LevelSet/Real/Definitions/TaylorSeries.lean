import CORALean.ContSet.Interval.Real.Operations.Center
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The Taylor series operator

[1, Def. 7]: `a, b, c, v(·), l, u ← taylor(f(·), I, κ)` expands `f` around `c = center(I)`:
`b = f(c)`, `aᵀ(x - c)` the first-order term, `v(x)` the terms of order `2 … κ`, each
`((x - c)ᵀ∇)ⁱ f(c) / i!` — here `Dⁱf(c)(x - c, …, x - c) / i!` — and `[l, u]` any interval
containing [1]'s Lagrange remainder set
`L = {((x - c)ᵀ∇)^{κ+1} f(ξ) / (κ+1)! | ξ ∈ I, x ∈ I}`.

`b` is `f(c)` itself, and `a` and `v` are determined by `f`, `I` and `κ`, so they are
definitions; `[l, u]` is whatever enclosure an interval evaluation of `L` returns, so
`TaylorSeries` carries it with the proof that it encloses `L`. The enclosure [1] then states,
`∀ x ∈ I : f(x) ∈ b + aᵀ(x - c) + v(x) ⊕ [l, u]`, is `Theorems.TaylorSeriesMem`, which needs
more of `f` than [1]'s Lipschitz continuity.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a`, the gradient at `c`, read coordinate by coordinate. -/
noncomputable def taylorGrad (f : Vec ℝ n → ℝ) (c : Vec ℝ n) : Vec ℝ n :=
  fun i => fderiv ℝ f c (Pi.single i 1)

/-- `v(x) = Σ_{i=2}^{κ} ((x - c)ᵀ∇)ⁱ f(c) / i!`. -/
noncomputable def taylorHigher (f : Vec ℝ n → ℝ) (κ : ℕ) (c x : Vec ℝ n) : ℝ :=
  ∑ i ∈ Finset.Icc 2 κ, iteratedFDeriv ℝ i f c (fun _ => x - c) / (i.factorial : ℝ)

/-- The Lagrange remainder set `L`: the order-`κ+1` term at any `ξ ∈ X` and any `x ∈ X`. -/
def lagrangeSet (f : Vec ℝ n → ℝ) (κ : ℕ) (c : Vec ℝ n) (X : Set (Vec ℝ n)) : Set ℝ :=
  {y | ∃ ξ ∈ X, ∃ x ∈ X,
    y = iteratedFDeriv ℝ (κ + 1) f ξ (fun _ => x - c) / ((κ + 1).factorial : ℝ)}

/-- What `taylor(f, I, κ)` returns beyond `b`, `a`, `c` and `v`: an interval `[l, u] ⊇ L`. -/
structure TaylorSeries (f : Vec ℝ n → ℝ) (I : Interval (Vec ℝ n)) (κ : ℕ) where
  l : ℝ
  u : ℝ
  encloses : ∀ y ∈ lagrangeSet f κ I.center I.construct, l ≤ y ∧ y ≤ u

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
