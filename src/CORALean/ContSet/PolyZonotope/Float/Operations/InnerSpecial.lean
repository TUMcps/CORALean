import CORALean.ContSet.PolyZonotope.Float.Operations.InnerTest

/-!
# `PolyZonotope.innerSpecial`

CORA's `aux_InnerSpecial` in `innerApproxImage`, [1, Alg. 2]: the function and its domain have
the same dimension, `C = inv(df(x_))` preconditions the whole Jacobian, and the inflation loop
runs on all of `X_` (`innerTest` with `ind` the identity). `df(x_)` is the midpoint of the
interval Jacobian at the point `x_`; `inv` is the caller's approximate inverse, which
`innerTest` certifies before trusting.

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

/-- [1, Alg. 2] as `aux_InnerSpecial` runs it. -/
def PolyZonotope.innerSpecial (pZ : PolyZonotope 𝕋 n) (X X₀ : Interval (Vec 𝕋 pZ.p))
    (Y : Interval (Vec 𝕋 n)) (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ)
    (h : n = pZ.p) : Bool :=
  -- every coordinate is `u₁`
  let ind : Fin n ↪ Fin pZ.p := ⟨Fin.cast h, Fin.cast_injective h⟩
  -- x_ = center(X_)
  let xc : Vec 𝕋 pZ.p := Interval.center X₀
  -- df(x_)
  let Jc := PolyZonotope.jacobianBox pZ (Interval.point xc)
  let M : Mat 𝕋 n n := fun i j => half (addUp (Jc.inf i (ind j)) (Jc.sup i (ind j)))
  -- C = inv(df(x_))
  let C : Mat 𝕋 n n := inv M
  PolyZonotope.innerTest pZ X X₀ Y ind M C iter

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
