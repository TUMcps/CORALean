import CORALean.ContSet.PolyZonotope.Float.Operations.InnerColumns
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerTest

/-!
# `PolyZonotope.innerGeneral`

CORA's `aux_InnerGeneral` in `innerApproxImage` and `aux_containsInterval` in
`@polyZonotope/contains_`, [1, Alg. 3]: the domain has more dimensions than the function, so
`aux_getSuitableSubmatrix` (`innerColumns`) picks the columns of `u₁` from `df(X_)`, the
preconditioner is the inverse of those columns of `df(x_)` (`aux_preconditionMatrix`, the
`r × r` block [1, Eq. 10] needs), and the inflation loop (`innerTest`) runs on `U1_`; if it fails,
once more without preconditioning (`C = eye(n)`). CORA falls back to `eye(n)` when the extended
Jacobian is rank-deficient; here an inverse `innerTest` cannot certify fails that pass, and the
retry is the same.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
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

/-- [1, Alg. 3] as `aux_InnerGeneral` runs it. -/
def PolyZonotope.innerGeneral (pZ : PolyZonotope (Vec 𝕋 n)) (X X₀ : Interval (Vec 𝕋 pZ.p))
    (Y : Interval (Vec 𝕋 n)) (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ) : Bool :=
  -- ind = aux_getSuitableSubmatrix(df(X_), n)
  match PolyZonotope.innerColumns (PolyZonotope.jacobianBox pZ X₀) with
  | none => false
  | some ind =>
    -- x_ = center(X_), and df(x_) at the columns `ind`
    let xc : Vec 𝕋 pZ.p := Interval.center X₀
    let Jc := PolyZonotope.jacobianBox pZ (Interval.point xc)
    let M : Mat 𝕋 n n := fun i j => half (addUp (Jc.inf i (ind j)) (Jc.sup i (ind j)))
    -- C = aux_preconditionMatrix(df, X_, ind, n)
    let C : Mat 𝕋 n n := inv M
    -- eye(n)
    let I : Mat 𝕋 n n := fun i j => if i = j then one else zero
    -- the test, and aux_InnerGeneral(f,df,X,X_,Y_,'none') if it fails
    PolyZonotope.innerTest pZ X X₀ Y ind M C iter || PolyZonotope.innerTest pZ X X₀ Y ind I I iter

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
