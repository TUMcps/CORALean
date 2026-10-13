import CORALean.NN.Layers.Definitions.StarSet

/-!
# The bounds of one neuron as CORA's code computes them

`c_ = c(j) + 0.5 * G(j,:) * (u_ - l_)`, `G_ = 0.5 * G(j,:) * diag(u_-l_)`, `l = c_ - sum(abs(G_))`
and `u = c_ + sum(abs(G_))` in `nnReLULayer/evaluateConZonotopeNeuron`, with `bound_approx`
true. The centre of the factor box is `(l_ + u_)/2`, not `(u_ - l_)/2`: with `l_ = -1`, `u_ = 1`,
which is what `conversionConZonoStarSet` returns for a constrained zonotope without equality
constraints, the code's centre is `c(j) + sum(G(j,:))`, and the interval it returns is the true
one shifted by `sum(G(j,:))`. It is the true interval only where `l_ = 0`, which the factors
a step appends have. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def StarSet.coraRowBounds {n : ℕ} (s : StarSet n) (j : Fin n) : ℝ × ℝ :=
  let c_ := s.c j + (1 / 2) * ∑ k, s.G j k * (s.u k - s.l k)
  let r := ∑ k, |(1 / 2) * s.G j k * (s.u k - s.l k)|
  (c_ - r, c_ + r)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
