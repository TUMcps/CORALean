module

public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerApproxImage
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `PolyZonotope.innerApprox`

CORA's `@polyZonotope/innerApprox`: the boxes `innerApproxImage` proves inside the image of the
factor cube `[-1, 1]ᵖ` under the dependent point map, each turned into a zonotope and shifted by
the independent generators, `zonotope(S{i}) + zonotope(0, GI)`. The union of the zonotopes is an
inner approximation.

The conversion of a box to a zonotope rounds inward: the centre is the rounded midpoint, kept
only where it lies in the box, and the radius in each coordinate is the smaller distance to the
two bounds, rounded down and at least `0`; the error box is `0`, so nothing is added outward.
Where the stored error box does not hold `0`, the nominal set need not lie in the set, and the
result is empty. `tol` is CORA's (default `max(rad(X))/100`); `inv`, `iter` and `depth` are
the approximate inverse and the caps `innerApproxImage` takes.
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
  if (List.finRange n).all fun i => le (pZ.err.inf i) zero && le zero (pZ.err.sup i) then
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
