module

public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerStep
public import CORALean.ContSet.PolyZonotope.Float.Operations.PointBox
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `PolyZonotope.innerTest`

The domain-inflation loop of [1, Alg. 3] as CORA's `aux_InnerGeneral` and `aux_containsInterval`
run it for the dependent point map `f`: with the columns `ind` of the Jacobian as `u₁`, the box
`Y` is proved inside `f(X)` when `t = Diag⁻¹(J₁)(b - OffDiag(J₁)(U1_ - u1_)) - J₂(U2_ - u2_)`
lands in `U1_`; otherwise `U1_ ← u1_ + τt` while the distance contracts by `μ`; `innerStep` is
the body. CORA's `while` has no bound; `iter` caps it. CORALean also checks that `C` is
nonsingular (`aux_precondRegular`), that `x_` lies in `X` and `X_` off `ind`, and `u1_ ∈ U1_`.

## Inputs
* `pZ` – polynomial zonotope
* `X` – factor box
* `X₀` – inner factor box
* `Y` – target box
* `ind` – selected factor indices
* `M` – midpoint Jacobian
* `C` – approximate inverse Jacobian
* `iter` – number of iterations

## Output
* Boolean, true only if the inclusion test succeeds

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every row of `|1 - M C|` sums to less than `1`, so `C` is injective. -/
def PolyZonotope.aux_precondRegular (M C : Mat 𝕋 n n) : Bool :=
  -- `M C`, rounded both ways
  let lo := matMulDown M C
  let hi := matMulUp M C
  -- an upper bound of `|(1 - M C)ᵢⱼ|`
  let r : Fin n → Fin n → 𝕋 := fun i j =>
    maximum (absolute (subDown (if i = j then one else zero) (hi i j)))
      (absolute (subUp (if i = j then one else zero) (lo i j)))
  (List.finRange n).all fun i => ltStrict (sumUp (r i)) one


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] as CORA runs it: `true` proves `Y ⊆ f(X)` for the dependent point map `f`. -/
def PolyZonotope.innerTest (pZ : PolyZonotope (Vec 𝕋 n)) (X X₀ : Interval (Vec 𝕋 pZ.p))
    (Y : Interval (Vec 𝕋 n)) (ind : Fin n ↪ Fin pZ.p) (M C : Mat 𝕋 n n) (iter : ℕ) : Bool :=
  -- 1. `τ ← 1.01`, `μ ← 0.9` (`μ` squared, as distances are)
  let τ : 𝕋 := divUp (nsmulUp 101 one) (nsmulUp 100 one)
  let μsq : 𝕋 := divUp (nsmulUp 81 one) (nsmulUp 100 one)
  -- 3. `x̃ ← mid(x̃)`
  let xc : Vec 𝕋 pZ.p := Interval.center X₀
  -- 7. `(ũ₁, ũ₂) ← Extract(x̃, r, m)`, 9. `(u₁, u₂) ← Extract(x, r, m)`, and the same for `x̃`
  let u1c : Vec 𝕋 n := fun i => xc (ind i)
  let U1 : Interval (Vec 𝕋 n) := ⟨fun i => X.inf (ind i), fun i => X.sup (ind i)⟩
  let U1₀ : Interval (Vec 𝕋 n) := ⟨fun i => X₀.inf (ind i), fun i => X₀.sup (ind i)⟩
  -- 11. `b ← C ỹ - C f(x̃)`
  let b : Interval (Vec 𝕋 n) := ((Interval.mtimes C Y).minus
    (Interval.mtimes C (PolyZonotope.pointBox pZ (Interval.point xc)))).materialise
  -- 6. `C` is checked nonsingular, and `x̃` in `x` and `x̃` off `ind` (soundness, not printed)
  let ok : Bool := PolyZonotope.aux_precondRegular M C && (List.finRange pZ.p).all fun k =>
    (List.finRange n).any (fun i => decide (ind i = k)) || (le (X.inf k) (xc k)
      && le (xc k) (X.sup k) && le (X₀.inf k) (xc k) && le (xc k) (X₀.sup k))
  -- 12. the distance `d(ũ, ũ + τt)` of line 17, squared
  let dist : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n) → 𝕋 := fun U V => sumUp fun i =>
    let e := maximum (absolute (subUp (U.sup i) (V.sup i))) (absolute (subUp (U.inf i) (V.inf i)))
    mulUp e e
  -- 13. `d_k ≤ μ d_{k-1}`, `none` read as `+∞`
  let contracts : Option 𝕋 → Option 𝕋 → Bool := fun d₁ d₂ => match d₁, d₂ with
    | some a, some c => le c (mulUp μsq a)
    | _, _ => true
  -- 13. one pass of the `while` loop: the current `ũ₁`, `d_{k-1}`, `d_k`, and the answer once known
  let step : Interval (Vec 𝕋 n) × Option 𝕋 × Option 𝕋 × Option Bool →
      Interval (Vec 𝕋 n) × Option 𝕋 × Option 𝕋 × Option Bool := fun s =>
    match s with
    | (U, d₁, d₂, none) =>
      if contracts d₁ d₂ && Interval.le U U1 then
        match PolyZonotope.innerStep pZ X₀ ind C xc b U with
        | none => (U, d₁, d₂, some false)
        | some t =>
          -- 15. if `ũ + t ⊆ ũ` return true
          if Interval.le ((Interval.point u1c).plus t) U then
            (U, d₁, d₂, some (Interval.le (Interval.point u1c) U))
          else
            -- 16. `d_{k-1} ← d_k`, 17. `d_k ← d(ũ, ũ + τt)`, 18. `ũ ← ũ + τt`
            let U' : Interval (Vec 𝕋 n) := Interval.materialise
              ⟨fun i => addDown (u1c i) (mulDown τ (t.inf i)),
                fun i => addUp (u1c i) (mulUp τ (t.sup i))⟩
            (U', d₂, some (dist U U'), none)
      else (U, d₁, d₂, some false)
    | s => s
  -- 20. return false once the loop is left; the loop runs on `iter`, which caps it
  ok && ((step^[iter] (U1₀, none, none, none)).2.2.2 == some true)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
