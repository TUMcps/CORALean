module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.SplitAt
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerGeneral
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerSpecial

@[expose] public section

/-!
# `PolyZonotope.innerApproxImage`

CORA's `innerApproxImage` for the dependent point map `f` of a polynomial zonotope, the bisection
of [2, Alg. 1] (restated as [1, Alg. 1]): for a box `X_` of the domain,
`Y_ = f(X_) & (f(c) + df(X_)(X_ - c))` encloses its image; if `Inner` proves `Y_ ⊆ f(X)` the
box `Y_` is kept, else `X_` is split at its widest coordinate while its narrowest radius is at
least `tol`. `Inner` is `aux_InnerSpecial`
(`innerSpecial`) when `f` and the domain have the same dimension, `aux_InnerGeneral`
(`innerGeneral`) when the domain is larger; CORA throws when it is smaller, and the result here
is empty. CORA's worklist runs breadth first and this recursion depth first, which reorders the
list and keeps every box; `depth` caps the recursion, which CORA bounds by `tol` alone.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
* [2] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
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

/-- [2, Alg. 1] as `innerApproxImage` runs it, from the box `X₀` of the domain `X`. -/
def PolyZonotope.innerApproxImage (pZ : PolyZonotope (Vec 𝕋 n))
    (X : Interval (Vec 𝕋 pZ.p)) (tol : 𝕋)
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ) :
    ℕ → Interval (Vec 𝕋 pZ.p) → List (Interval (Vec 𝕋 n))
  | 0, _ => []
  | depth + 1, X₀ =>
    -- 5. `x̃ ← Extract(LDomain)` is `X₀` (lines 1-4: the recursion from `{x}`); `c`, its midpoint
    let c : Vec 𝕋 pZ.p := Interval.center X₀
    -- 6. `ỹ ← f(x̃) ∩ (f(mid x̃) + f'(x̃)(x̃ - mid x̃))`
    let Y : Interval (Vec 𝕋 n) := ((PolyZonotope.pointBox pZ X₀).intersection
      ((PolyZonotope.pointBox pZ (Interval.point c)).plus
        ((PolyZonotope.jacobianBox pZ X₀).mtimesIntervalMat
          (X₀.minus (Interval.point c))))).materialise
    -- 7. `Inner(f, x, x̃, ỹ)`, as `innerSpecial` or `innerGeneral` by the dimensions
    let inner : Bool := if h : n = pZ.p then PolyZonotope.innerSpecial pZ X X₀ Y inv iter h
      else if n < pZ.p then PolyZonotope.innerGeneral pZ X X₀ Y inv iter else false
    -- 8. if it holds, store the box `ỹ` in `LInside`
    if inner then [Y] else
    -- 9. else if `‖rad x̃‖ ≥ ε`: the radius `rad x̃`, taken as the narrowest, against `tol`
    let r : Fin pZ.p → 𝕋 := fun k => half (subUp (X₀.sup k) (X₀.inf k))
    if (List.finRange pZ.p).all fun k => le tol (r k) then
      -- 10. bisect the box `x̃` into `x̃'` and `x̃''` at its first widest coordinate
      match (List.finRange pZ.p).foldl (fun best k => match best with
        | none => some k
        | some b => if le (r k) (r b) then some b else some k) none with
      | none => []
      | some k =>
        -- 11. store `x̃'` and `x̃''` in `LDomain`: the two halves are visited in turn
        PolyZonotope.innerApproxImage pZ X tol inv iter depth (X₀.splitAt k).1.materialise ++
          PolyZonotope.innerApproxImage pZ X tol inv iter depth (X₀.splitAt k).2.materialise
    -- 13. else `ỹ` would go to `LBoundary`, which is not computed
    else []

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
