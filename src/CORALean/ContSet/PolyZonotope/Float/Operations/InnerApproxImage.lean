import CORALean.ContSet.Interval.Float.Operations.Intersection
import CORALean.ContSet.Interval.Float.Operations.SplitAt
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerGeneral
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerSpecial

/-!
# `PolyZonotope.innerApproxImage`

CORA's `innerApproxImage` for the dependent point map `f` of a polynomial zonotope, the bisection
of [1, Alg. 1]: for a box `X_` of the domain, `Y_ = f(X_) & (f(c) + df(X_)(X_ - c))` encloses
its image; if `Inner` proves `Y_ ⊆ f(X)` the box `Y_` is kept, else `X_` is split at its widest
coordinate while its narrowest radius is at least `tol`. `Inner` is `aux_InnerSpecial`
(`innerSpecial`) when `f` and the domain have the same dimension, `aux_InnerGeneral`
(`innerGeneral`) when the domain is larger; CORA throws when it is smaller, and the result here
is empty. CORA's worklist runs breadth first and this recursion depth first, which reorders the
list and keeps every box; `depth` caps the recursion, which CORA bounds by `tol` alone.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] as `innerApproxImage` runs it, from the box `X₀` of the domain `X`. -/
def PolyZonotope.innerApproxImage (pZ : PolyZonotope 𝕋 n) (X : Interval (Vec 𝕋 pZ.p)) (tol : 𝕋)
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ) :
    ℕ → Interval (Vec 𝕋 pZ.p) → List (Interval (Vec 𝕋 n))
  | 0, _ => []
  | depth + 1, X₀ =>
    -- c = center(X_)
    let c : Vec 𝕋 pZ.p := Interval.center X₀
    -- Y_ = f(X_) & (f(center(X_)) + df(X_)*(X_-center(X_)))
    let Y : Interval (Vec 𝕋 n) := ((PolyZonotope.pointBox pZ X₀).intersection
      ((PolyZonotope.pointBox pZ (Interval.point c)).plus
        ((PolyZonotope.jacobianBox pZ X₀).mtimesIntervalMat
          (X₀.minus (Interval.point c))))).materialise
    -- Inner(f,df,X,X_,Y_)
    let inner : Bool := if h : n = pZ.p then PolyZonotope.innerSpecial pZ X X₀ Y inv iter h
      else if n < pZ.p then PolyZonotope.innerGeneral pZ X X₀ Y inv iter else false
    if inner then [Y] else
    -- rad(X_)
    let r : Fin pZ.p → 𝕋 := fun k => half (subUp (X₀.sup k) (X₀.inf k))
    -- min(rad(X_)) >= tol
    if (List.finRange pZ.p).all fun k => le tol (r k) then
      -- [~,dim] = max(rad(X_)), the first widest coordinate
      match (List.finRange pZ.p).foldl (fun best k => match best with
        | none => some k
        | some b => if le (r k) (r b) then some b else some k) none with
      | none => []
      | some k =>
        -- splitDomains = split(X_,dim)
        PolyZonotope.innerApproxImage pZ X tol inv iter depth (X₀.splitAt k).1.materialise ++
          PolyZonotope.innerApproxImage pZ X tol inv iter depth (X₀.splitAt k).2.materialise
    else []

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
