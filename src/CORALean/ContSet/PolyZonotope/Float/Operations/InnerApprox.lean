module

public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerApproxImage
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `PolyZonotope.innerApprox`

CORA's `@polyZonotope/innerApprox`: the boxes `innerApproxImage` proves inside the image of the
factor cube `[-1, 1]ᵖ` under the dependent point map, each turned into a zonotope and shifted by
the independent generators; the union is an inner approximation. A box becomes a zonotope by
rounding inward (center the rounded midpoint kept only inside the box, radius the smaller
distance to the bounds, rounded down, error box `0`); where the stored error box does not hold
`0`, the result is empty. `tol` is CORA's; `inv`, `iter` and `depth` are `innerApproxImage`'s.

## Inputs
* `pZ` – polynomial zonotope
* `tol` – tolerance
* `inv` – matrix inverse routine
* `iter` – number of iterations
* `depth` – splitting depth

## Output
* list of zonotopes proven inside the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Zonotopes whose union is inside `pZ`, as CORA's `innerApprox` computes them. -/
def PolyZonotope.innerApprox (pZ : PolyZonotope (Vec 𝕋 n)) (tol : 𝕋)
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter depth : ℕ) : List (Zonotope (Vec 𝕋 n)) :=
  -- D = interval(-ones(p,1), ones(p,1))
  let D : Interval (Vec 𝕋 pZ.p) := ⟨fun _ => neg one, fun _ => one⟩
  -- S = innerApproxImage(f, D, tol)
  let S := PolyZonotope.innerApproxImage pZ D tol inv iter depth D
  -- the error box holds `0`
  if (List.finRange n).all fun i => le (pZ.I_error.inf i) zero && le zero (pZ.I_error.sup i) then
    -- S{i} = zonotope(S{i}) + zonotope(zeros(dim(pZ),1), pZ.GI), rounded inward
    S.filterMap fun Y =>
      let c : Vec 𝕋 n := Interval.center Y
      let r : Vec 𝕋 n := fun i => maximum zero (minimum (subDown (Y.sup i) (c i))
        (subDown (c i) (Y.inf i)))
      if Interval.le (Interval.point c) Y then
        some ⟨n + pZ.q, c, Fin.append (fun j i => if i = j then r j else zero) pZ.GI,
          Interval.point fun _ => zero⟩
      else none
  else []

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
