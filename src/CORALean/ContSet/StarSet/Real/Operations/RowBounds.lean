module

public import CORALean.ContSet.StarSet.Real.StarSet
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The bounds of one neuron of a star set

CORA's `nnReLULayer/evaluateConZonotopeNeuron` with `options.nn.bound_approx` (its default) bounds
the neuron `j` over the factor box `[l, u]`: the centre of the row `c_j + G_j α` and its radius
`Σ |G_jk| (u_k - l_k) / 2`, and `l = centre - radius`, `u = centre + radius`. The centre of the
box is `(l + u) / 2`, which is what the row's centre is taken at here. CORA's code takes
`c_j + G_j (u - l) / 2` instead, which is the same only where `l = 0`: see
`StarSet.coraRowBounds`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def StarSet.rowBounds {n : ℕ} (s : StarSet n) (j : Fin n) : Interval ℝ :=
  let c_ := s.c j + ∑ k, s.G j k * ((s.l k + s.u k) / 2)
  let r := ∑ k, |s.G j k * ((s.u k - s.l k) / 2)|
  ⟨c_ - r, c_ + r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
