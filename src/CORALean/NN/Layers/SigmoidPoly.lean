import CORALean.NN.Layers.PolyDerivBound
import CORALean.NN.Layers.PolyFit
import CORALean.NN.Layers.Sigmoid

/-!
# The polynomial relaxation at the sigmoid

The first activation at which `PolyRelaxation.ofSampling` can actually be
instantiated. It asks for a bound on `|σ' - p'|` over the box, `Sigmoid` already
brackets `σ'` there, and `polyDerivDiff` is the two brackets subtracted, so
nothing beyond assembly is left.

Both the coefficients and the sample count stay parameters. Neither owes a
proof: any fit is sound once the bound holds, and any positive sample count is,
so a caller spends effort on the neurons that deserve it — which is what
`SigmoidPolyRefine` varies, one level at a time. `polyFit` is one such choice,
CORA's default, and `sigmoidPolyRelaxationFit` is the pipeline closed at it.

Nothing is given away against `Relaxation.ofDeriv` at order 1:
`polyDerivDiff_one` says the derivative bound is there exactly the bracket
`ofDeriv` works with, and the sampled range replaces `ofDeriv`'s worst case
`(hi - lo)(u - l)/2` by what `σ` less its secant spans — for the price of
enough samples that the padding `M · dx` is under that worst case.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- `ofSampling` at the sigmoid: `M` is the derivative bracket of `Sigmoid`
against the fit's own, the coefficients `c` and the sample count `N` free. -/
noncomputable def sigmoidPolyRelaxation {n : ℕ} (c : ℝ → ℝ → Fin (n + 1) → ℝ)
    (N : ℝ → ℝ → ℕ) (hN : ∀ l u, 0 < N l u) : PolyRelaxation sigmoid n :=
  PolyRelaxation.ofSampling hasDerivAt_sigmoid c
    (fun l u => polyDerivDiff (sigmoidDerivLo l u) (sigmoidDerivHi l u)
      (polyDerivCenter (c l u)) (polyDerivRadius (c l u) l u))
    N
    (fun _ _ _ hx hx' => abs_sub_evalPolyDeriv_le (sigmoidDerivLo_le hx hx')
      (le_sigmoidDerivHi hx hx') hx hx') hN

/-- The same at CORA's default fit, which leaves only the sample count to
choose. -/
noncomputable def sigmoidPolyRelaxationFit {n : ℕ} (N : ℝ → ℝ → ℕ) (hN : ∀ l u, 0 < N l u) :
    PolyRelaxation sigmoid n :=
  sigmoidPolyRelaxation (polyFit sigmoid n) N hN

end CORALean.Real
