module

public import CORALean.ContSet.StarSet.Real.StarSet
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The bounds of one neuron of a star set

CORA's `nnReLULayer/evaluateConZonotopeNeuron` with `options.nn.bound_approx` (its default) bounds
the neuron `j` over the coefficient box `[l, u]`: the center of the row `c_j + G_j α` and its radius
`Σ |G_jk| (u_k - l_k) / 2`, and `l = center - radius`, `u = center + radius`. The center of the
box is `(l + u) / 2`, which is what the row's center is taken at here. CORA's code takes
`c_j + G_j (u - l) / 2` instead, which is the same only where `l = 0`: see
`StarSet.coraRowBounds`.

## Inputs
* `P` – predicate family
* `n` – dimension
* `s` – star set
* `j` – neuron index

## Output
* interval bounds of neuron `j` over the factor box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def StarSet.rowBounds {P : ℕ → Type} {n : ℕ} (s : StarSet P n) (j : Fin n) :
    Interval ℝ :=
  let c_ := s.c j + ∑ k, s.G j k * ((s.dom.inf k + s.dom.sup k) / 2)
  let r := ∑ k, |s.G j k * ((s.dom.sup k - s.dom.inf k) / 2)|
  ⟨c_ - r, c_ + r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
