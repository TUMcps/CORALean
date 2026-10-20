module

public import CORALean.NN.Layers.Definitions.EvalPoly

@[expose] public section

/-!
# Bounding a fit's derivative over ℝ

`PolyRelaxation.ofSampling` asks for an `M` with `|σ' - p'| ≤ M` on the box. This is the
polynomial half of it, over ℝ: `evalPolyDeriv` bracketed around its linear coefficient — the
derivative's constant term, which no box widens — by a radius, every other monomial at the end
of the box furthest from zero and every sign taken against itself; `polyDerivDiff` is that
bracket against one for `σ'`, at the worse end. A center and a radius keep order 1 exact: the
radius is zero there, and the bracket is the one `Relaxation.ofDeriv` works with.

## Inputs
* `n` – polynomial degree
* `c` – coefficients of the fit

## Output
* the fit's linear coefficient
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The fit's linear coefficient, which at order 1 is the whole derivative. -/
noncomputable def polyDerivCenter {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), if (i : ℕ) = 1 then c i else 0

/-- How far the remaining monomials move that center over `[l, u]`. -/
noncomputable def polyDerivRadius {n : ℕ} (c : Fin (n + 1) → ℝ) (l u : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), if (i : ℕ) = 1 then 0
    else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)

/-- A bracket for `σ'` against the fit's own, the two subtracted at the worse end. -/
noncomputable def polyDerivDiff (lo hi ctr rad : ℝ) : ℝ :=
  max |lo - ctr - rad| |hi - ctr + rad|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
