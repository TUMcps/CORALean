import CORALean.NN.Layers.PolyAffineConj
import CORALean.NN.Layers.SigmoidPoly
import CORALean.NN.Layers.Tanh

/-!
# The polynomial relaxation at tanh

`tanh t = 2 σ (2 t) - 1` transports at every order, not only at the affine one:
`PolyRelaxation.ofAffineConj` rescales the coefficients and the error, and no
derivative bracket for tanh is stated here any more than one is in `Tanh`.

The fit rides along too: the sample grid of `[l, u]` maps onto that of
`[2l, 2u]`, and every residual scales by the same two, so the conjugate of the
least-squares fit of `σ` is the least-squares fit of `tanh`. Nothing rests on
that — the relaxation is sound at whatever coefficients the conjugation
produces — which is why it is said here and not proved.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- `sigmoidPolyRelaxation` read through `tanh t = 2 σ (2 t) - 1`: `a = b = 2`
and `d = -1`, as at order 1. -/
noncomputable def tanhPolyRelaxation {n : ℕ} (c : ℝ → ℝ → Fin (n + 1) → ℝ)
    (N : ℝ → ℝ → ℕ) (hN : ∀ l u, 0 < N l u) : PolyRelaxation Real.tanh n :=
  (sigmoidPolyRelaxation c N hN).ofAffineConj (a := 2) (b := 2) (d := -1)
    (by norm_num) (by norm_num) fun t => by rw [tanh_eq_sigmoid]; ring

/-- The same at CORA's default fit of the sigmoid, conjugated. -/
noncomputable def tanhPolyRelaxationFit {n : ℕ} (N : ℝ → ℝ → ℕ) (hN : ∀ l u, 0 < N l u) :
    PolyRelaxation Real.tanh n :=
  tanhPolyRelaxation (polyFit sigmoid n) N hN

end CORALean.Real
