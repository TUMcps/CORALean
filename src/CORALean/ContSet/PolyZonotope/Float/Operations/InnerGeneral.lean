module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerTest
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# `PolyZonotope.innerGeneral`

CORA's `aux_InnerGeneral` in `innerApproxImage` and `aux_containsInterval` in
`@polyZonotope/contains_`, [1, Alg. 3]: the domain has more dimensions than the function, so
`aux_getSuitableSubmatrix` (`aux_innerColumns`) picks the columns of `u₁` from `df(X_)`, the
preconditioner is the inverse of those columns of `df(x_)` (`aux_preconditionMatrix`, the
`r × r` block [1, Eq. 10] needs), and the inflation loop (`innerTest`) runs on `U1_`; if it fails,
once more without preconditioning (`C = eye(n)`). CORA falls back to `eye(n)` when the extended
Jacobian is rank-deficient; here an inverse `innerTest` cannot certify fails that pass, and the
retry is the same.

## Inputs
* `pZ` – polynomial zonotope
* `X` – factor box
* `X₀` – inner factor box
* `Y` – target box
* `inv` – matrix inverse routine
* `iter` – number of iterations

## Output
* Boolean, true only if the target box is shown inside the image

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}
variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One column per row at an entry without `0`, as `aux_getSuitableSubmatrix` picks them. -/
def PolyZonotope.aux_innerColumns (J : Interval (Mat 𝕋 n m)) : Option (Fin n ↪ Fin m) :=
  -- nonZero(i,j) = ~contains(J(i,j),0)
  let nz : Fin n → Fin m → Bool := fun i j => !(le (J.inf i j) zero && le zero (J.sup i j))
  -- [~,index] = sort(sum(nonZero,2))
  let cnt : Fin n → ℕ := fun i => ((List.finRange m).filter (nz i)).length
  let index : List (Fin n) := (List.finRange n).mergeSort fun a b => decide (cnt a ≤ cnt b)
  -- ind(index(i)) = j for the last j not yet in `ind` with nonZero(index(i), j)
  let pairs : List (Fin n × Fin m) := index.foldl (fun acc i =>
    match (List.finRange m).reverse.find? (fun j => !(acc.any fun q => q.2 == j) && nz i j) with
    | some j => acc ++ [(i, j)]
    | none => acc) []
  let indOpt : Fin n → Option (Fin m) := fun i => (pairs.find? fun q => q.1 == i).map Prod.snd
  -- ismember(0,ind)
  if hall : ∀ i, (indOpt i).isSome then
    let ind : Fin n → Fin m := fun i => (indOpt i).get (hall i)
    if hinj : Function.Injective ind then some ⟨ind, hinj⟩ else none
  else none


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] as `aux_InnerGeneral` runs it. -/
def PolyZonotope.innerGeneral (pZ : PolyZonotope (Vec 𝕋 n)) (X X₀ : Interval (Vec 𝕋 pZ.p))
    (Y : Interval (Vec 𝕋 n)) (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ) : Bool :=
  -- 7. split `u` into `(u₁, u₂)` at the columns `ind` of `f'(x̃)` (lines 7-10)
  match PolyZonotope.aux_innerColumns (PolyZonotope.jacobianBox pZ X₀) with
  | none => false
  | some ind =>
    -- 3. `x̃ ← mid(x̃)`, and 5. `f'(x̃)` at the columns `ind` (the first `r` lines of the Jacobian)
    let xc : Vec 𝕋 pZ.p := Interval.center X₀
    let Jc := PolyZonotope.jacobianBox pZ (Interval.point xc)
    let M : Mat 𝕋 n n := fun i j => half (addUp (Jc.inf i (ind j)) (Jc.sup i (ind j)))
    -- 6. `C ← precondition(J_{f1:r})`
    let C : Mat 𝕋 n n := inv M
    -- 6. the identity, `C = eye(n)`: the preconditioner of the retry without preconditioning
    let I : Mat 𝕋 n n := fun i j => if i = j then one else zero
    -- 11. lines 11-20: `b` and the loop (`innerTest`); retried with `C = eye(n)` on failure
    PolyZonotope.innerTest pZ X X₀ Y ind M C iter || PolyZonotope.innerTest pZ X X₀ Y ind I I iter

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
