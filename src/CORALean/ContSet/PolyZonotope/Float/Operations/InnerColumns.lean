import CORALean.ContSet.Interval.Float.Interval
import Mathlib.Data.Fintype.Card

/-!
# `PolyZonotope.innerColumns`

CORA's `aux_getSuitableSubmatrix` (in `innerApproxImage` and `@polyZonotope/contains_`): `n`
distinct columns of the `n × m` interval Jacobian, one per row, each at an entry that does not
hold `0`. The rows are taken in increasing order of how many such entries they have (`sort`,
which is stable, as `mergeSort` is), and each row takes the last column no earlier row has
taken; `none` where a row finds none (CORA's `ismember(0,ind)`). The heuristic only picks `u₁`
of [1, Alg. 3]; the test's soundness does not depend on it.

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

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One column per row at an entry without `0`, as `aux_getSuitableSubmatrix` picks them. -/
def PolyZonotope.innerColumns (J : Interval (Mat 𝕋 n m)) : Option (Fin n ↪ Fin m) :=
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
