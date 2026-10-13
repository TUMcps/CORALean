import CORALean.ContSet.Interval.Float.Operations.Center
import CORALean.ContSet.Interval.Float.Operations.Le
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerStep
import CORALean.ContSet.PolyZonotope.Float.Operations.PointBox
import CORALean.ContSet.PolyZonotope.Float.Operations.PrecondRegular

/-!
# `PolyZonotope.innerTest`

The domain-inflation loop of [1, Alg. 3] as CORA's `aux_InnerGeneral` (in `innerApproxImage`)
and `aux_containsInterval` (in `@polyZonotope/contains_`) run it for the dependent point map `f`:
with the columns `ind` of the Jacobian as `u₁`, the box `Y` (`Y_`) is proved inside `f(X)` when
`t = Diag⁻¹(J₁)(b - OffDiag(J₁)(U1_ - u1_)) - J₂(U2_ - u2_)` lands in `U1_`, `J = C·df(X_mod)`,
`b = C·Y - C·f(x_)`; otherwise `U1_ ← u1_ + τt` while the distance contracts by `μ` and `U1_`
stays in `X`; `innerStep` is the body. `ind` the identity is `aux_InnerSpecial`'s loop
([1, Alg. 2]).

CORA's `while` has no bound; `iter` caps it. The test proves a pre-image of `C·y` only, and the
closed inclusion needs `u1_ ∈ U1_` and the slice in `X` and `X_`, so CORALean also checks that
`C` is nonsingular (`precondRegular` against `M`, which `C` should invert), that `x_` lies in `X`
and `X_` off `ind`, and that `u1_ ∈ U1_` at acceptance. Distances are compared squared. With
`J₂(U2_ - u2_) ∋ 0`, the test is `exists_jacobiSlice_eq_of_jacobi` on the slice at `u2_`.

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

/-- [1, Alg. 3] as CORA runs it: `true` proves `Y ⊆ f(X)` for the dependent point map `f`. -/
def PolyZonotope.innerTest (pZ : PolyZonotope (Vec 𝕋 n)) (X X₀ : Interval (Vec 𝕋 pZ.p))
    (Y : Interval (Vec 𝕋 n)) (ind : Fin n ↪ Fin pZ.p) (M C : Mat 𝕋 n n) (iter : ℕ) : Bool :=
  -- tau = 1.01; mu = 0.9 (squared)
  let τ : 𝕋 := divUp (nsmulUp 101 one) (nsmulUp 100 one)
  let μsq : 𝕋 := divUp (nsmulUp 81 one) (nsmulUp 100 one)
  -- x_ = center(X_)
  let xc : Vec 𝕋 pZ.p := Interval.center X₀
  -- [u1_, u2_] = aux_Extract(x_), [U1, ~] = aux_Extract(X), [U1_, U2_] = aux_Extract(X_)
  let u1c : Vec 𝕋 n := fun i => xc (ind i)
  let U1 : Interval (Vec 𝕋 n) := ⟨fun i => X.inf (ind i), fun i => X.sup (ind i)⟩
  let U1₀ : Interval (Vec 𝕋 n) := ⟨fun i => X₀.inf (ind i), fun i => X₀.sup (ind i)⟩
  -- b = C*Y_ - C*f(x_)
  let b : Interval (Vec 𝕋 n) := ((Interval.mtimes C Y).minus
    (Interval.mtimes C (PolyZonotope.pointBox pZ (Interval.point xc)))).materialise
  -- C nonsingular, and x_ in X and X_ off `ind`
  let ok : Bool := PolyZonotope.precondRegular M C && (List.finRange pZ.p).all fun k =>
    (List.finRange n).any (fun i => decide (ind i = k)) || (le (X.inf k) (xc k)
      && le (xc k) (X.sup k) && le (X₀.inf k) (xc k) && le (xc k) (X₀.sup k))
  -- d(U1_, U1_'), squared
  let dist : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n) → 𝕋 := fun U V => sumUp fun i =>
    let e := maximum (absolute (subUp (U.sup i) (V.sup i))) (absolute (subUp (U.inf i) (V.inf i)))
    mulUp e e
  -- d(2) <= mu*d(1), `none` read as `Inf`
  let contracts : Option 𝕋 → Option 𝕋 → Bool := fun d₁ d₂ => match d₁, d₂ with
    | some a, some c => le c (mulUp μsq a)
    | _, _ => true
  -- one pass of the `while` body: the current `U1_`, `d(1)`, `d(2)`, and the answer once known
  let step : Interval (Vec 𝕋 n) × Option 𝕋 × Option 𝕋 × Option Bool →
      Interval (Vec 𝕋 n) × Option 𝕋 × Option 𝕋 × Option Bool := fun s =>
    match s with
    | (U, d₁, d₂, none) =>
      if contracts d₁ d₂ && Interval.le U U1 then
        match PolyZonotope.innerStep pZ X₀ ind C xc b U with
        | none => (U, d₁, d₂, some false)
        | some t =>
          -- contains_(U1_, u1_ + t)
          if Interval.le ((Interval.point u1c).plus t) U then
            (U, d₁, d₂, some (Interval.le (Interval.point u1c) U))
          else
            -- U1_ = u1_ + tau*t, d(1) = d(2), d(2) = aux_dist(U1_, u1_ + tau*t)
            let U' : Interval (Vec 𝕋 n) := Interval.materialise
              ⟨fun i => addDown (u1c i) (mulDown τ (t.inf i)),
                fun i => addUp (u1c i) (mulUp τ (t.sup i))⟩
            (U', d₂, some (dist U U'), none)
      else (U, d₁, d₂, some false)
    | s => s
  ok && ((step^[iter] (U1₀, none, none, none)).2.2.2 == some true)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
