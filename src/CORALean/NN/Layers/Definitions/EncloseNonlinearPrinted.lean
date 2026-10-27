module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.NN.Layers.Definitions.ApproxError
public import CORALean.NN.Layers.Definitions.SecantSlope

@[expose] public section

/-!
# Alg. 1 as printed, in one dimension

[1, Alg. 1] with its lines as printed, for `n = 1`: the bounds of `H` [1, Prop. 2], the secant
slope [1, Def. 7], the errors `e`, `ē` [1, Def. 6]; line 6 `H̃ = m H + ½(e + ē)` and line 7
`H = H̃ ⊕ [e, ē]`, which by [1, Prop. 3] has center `c̃ + ½(e + ē)` and the generators of `H̃`
and `½(ē - e)`. The midpoint is added by both lines.

## Inputs
* `ϕ` – activation function
* `H` – input zonotope

## Output
* zonotope Alg. 1 prints for the activation

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../../references/2025/koller-tmlr-set-based-training.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def encloseNonlinearPrinted (ϕ : ℝ → ℝ) (H : Zonotope (Vec ℝ 1)) :
    Zonotope (Vec ℝ 1) :=
  let l := H.c 0 - ∑ j, |H.G j 0|                                  -- line 2
  let u := H.c 0 + ∑ j, |H.G j 0|
  let m := secantSlope ϕ l u                                       -- line 4
  let e := approxErrorLow ϕ (fun x => m * x) l u                   -- line 5
  let e' := approxErrorUp ϕ (fun x => m * x) l u
  let c6 := m * H.c 0 + (e + e') / 2                               -- line 6
  { h := H.h + 1                                                   -- line 7
    c := fun _ => c6 + (e + e') / 2
    G := Fin.append (fun j _ => m * H.G j 0) (fun _ _ => (e' - e) / 2) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
