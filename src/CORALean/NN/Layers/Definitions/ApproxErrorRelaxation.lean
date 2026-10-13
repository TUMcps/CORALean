module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.NN.Layers.Definitions.ApproxError
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Definitions.SecantSlope

@[expose] public section

/-!
# The image enclosure of a nonlinear layer, as a relaxation

[1, Alg. 1]: per neuron, the slope `m = (ϕ(u) - ϕ(l)) / (u - l)` of the secant [1, Def. 7], and the
approximation errors `e_low`, `e_up` of `p(x) = m x` on `[l, u]` [1, Def. 6], the image being
enclosed by `m x ⊕ [e_low, e_up]`. As a `Relaxation`: slope `m`, offset `(e_low + e_up)/2` and error
`(e_up - e_low)/2`, the box `[e_low, e_up]` centred. `Layer.activation` of it is the algorithm:
the slope matrix applied to the input set, the box of errors added by one Minkowski sum.

The printed line 6 adds `(e_low + e_up)/2` to the centre of `Diag(m) H` and line 7 then forms
`⊕ [e_low, e_up]`, which by [1, Prop. 3] adds the midpoint again; the relaxation adds it once.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Slope `m`, offset `(e_low + e_up)/2`, error `(e_up - e_low)/2`. -/
noncomputable def approxErrorRelaxation (ϕ : ℝ → ℝ) : Relaxation ℝ where
  slope l u := secantSlope ϕ l u
  offset l u := (approxErrorLow ϕ (fun x => secantSlope ϕ l u * x) l u +
    approxErrorUp ϕ (fun x => secantSlope ϕ l u * x) l u) / 2
  error l u := (approxErrorUp ϕ (fun x => secantSlope ϕ l u * x) l u -
    approxErrorLow ϕ (fun x => secantSlope ϕ l u * x) l u) / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
