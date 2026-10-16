module

public import CORALean.ContSet.PolyZonotope.Float.Operations.BoxOut

@[expose] public section

/-!
# `PolyZonotope.outerApprox`, over a floating-point scalar

CORA's `outerApprox(pZ, tol, id)`: the dependent generators that depend on a factor outside `id`
and the independent ones are ranked by their `1`-norm (the columns of even monomials halved, as
CORA does), the scan takes the smallest while the running sum stays below `tol` times the largest
entry per coordinate, and the taken ones leave for a box (`PolyZonotope.boxOut`). The ranking and
the scan compare rounded sums with the certified `le`; they only choose the generators, and
`boxOut_outer` holds for every choice, so the guarantee does not depend on them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- How many of the sorted columns the scan takes: one is taken while the running sum plus its
absolute value stays below `Th` in every coordinate. -/
def PolyZonotope.aux_outerApproxCount (Th : Vec 𝕋 n) : List (Vec 𝕋 n) → Vec 𝕋 n → ℕ
  | [], _ => 0
  | g :: gs, v =>
    if (List.finRange n).all (fun k => FloatOps.le (addUp (absolute (g k)) (v k)) (Th k)) then
      1 + PolyZonotope.aux_outerApproxCount Th gs (fun k => addUp (v k) (absolute (g k)))
    else 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `outerApprox(pZ, tol, id)`. -/
def PolyZonotope.outerApprox (pZ : PolyZonotope (Vec 𝕋 n)) (tol : 𝕋) (S : Finset (Fin pZ.p)) :
    PolyZonotope (Vec 𝕋 n) :=
  -- `ii`: the dependent generators that depend on a factor outside `id`
  let dep : Fin pZ.h → Bool := fun i => decide (∃ k, k ∉ S ∧ 0 < pZ.E k i)
  -- `ind_even`: the monomial is even in every factor, so it lies in `[0, 1]`
  let even : Fin pZ.h → Bool := fun i => decide (∀ k, pZ.E k i % 2 = 0)
  -- the candidates `[G(:,ii), GI]`
  let cand : List (Fin pZ.h ⊕ Fin pZ.q) :=
    ((List.finRange pZ.h).filter dep).map Sum.inl ++ (List.finRange pZ.q).map Sum.inr
  -- `GGI`, the even columns halved
  let GGI : Fin pZ.h ⊕ Fin pZ.q → Vec 𝕋 n
    | Sum.inl i => fun k => if even i then half (pZ.G i k) else pZ.G i k
    | Sum.inr j => pZ.GI j
  -- `sort(sum(abs(GGI),1),'ascend')`
  let sorted : List (Fin pZ.h ⊕ Fin pZ.q) :=
    cand.mergeSort fun s t =>
      FloatOps.le (sumUp fun k => absolute (GGI s k)) (sumUp fun k => absolute (GGI t k))
  -- `Th = max(abs(GGI),[],2)*tol`
  let Th : Vec 𝕋 n := fun k =>
    mulUp tol ((cand.map fun t => absolute (GGI t k)).foldr maximum zero)
  -- `redCount`: the scan over the sorted columns
  let redCount : ℕ :=
    PolyZonotope.aux_outerApproxCount Th (sorted.map fun t k => absolute (GGI t k)) (fun _ => zero)
  -- `ii_red`
  let red : List (Fin pZ.h ⊕ Fin pZ.q) := sorted.take redCount
  -- `ii_red_G`, `ii_red_GI`: the removed dependent and the taken independent generators
  pZ.boxOut (fun i => red.any fun t => decide (t = Sum.inl i))
    (fun j => red.any fun t => decide (t = Sum.inr j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
