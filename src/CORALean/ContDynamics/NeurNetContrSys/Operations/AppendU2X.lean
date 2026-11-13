module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# The network's image appended to the state: CORA's `aux_appendU2X`, at zonotopes

CORA's `neurNetContrSys/reach` hands the plant not the product `X × U` but the zonotope
`[X.c; U.c]` with generators `[X.G 0; U.G]`: the network's image `U`, whose first generators are
the images of `X`'s ([1, Alg. 2]), keeps the dependence of the input on the state. That is sound
only for an image
that keeps `X`'s generators in front (`Zonotope.Tracks`), which the linear and the
activation layers do (`Layer.Tracks`) and `appendU2X_mem` uses: the joint set then holds
`[x; π(x)]`. Where `U` has fewer generators than `X`, CORA's `zeros` of a negative size fails,
here `none`. The error boxes are stacked, as in `Zonotope.cartProd`.

## Inputs
* `X` – state set
* `U` – network image of the state set, `X`'s generators first

## Output
* the joint zonotope of the state and the network output, or none

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[X.c; U.c]` with the generators `[X.G 0; U.G]`, or `none` if `U` has fewer generators. -/
def NeurNetContrSys.appendU2X (X : Zonotope (Vec 𝕋 n)) (U : Zonotope (Vec 𝕋 m)) :
    Option (Zonotope (Vec 𝕋 (n + m))) :=
  if X.h ≤ U.h then
    some { h := U.h, c := Fin.append X.c U.c,
           G := fun j => Fin.append                                  -- the column j of [X.G 0; U.G]
             (if hj : j.val < X.h then X.G ⟨j.val, hj⟩ else fun _ => zero) (U.G j),
           I_error := Interval.append X.I_error U.I_error }
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
