module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.BoxOut
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.outerApprox`

CORA's `@polyZonotope/outerApprox(pZ, tol, id)`: the small generators that depend on a factor
outside `id` are boxed into the independent block. The candidates are the dependent generators with
a positive exponent in a factor outside `id` (`ii`), an even exponent column making the monomial lie
in `[0, 1]` and the candidate ranked by half its length, together with all independent generators.
They are sorted by their `1`-norm and taken in ascending order while their sum stays below
`Th = max |GGI| * tol` in every coordinate. `boxOut` removes the taken dependent generators and
appends the box. The taken independent generators stay in `GI`, so their radius is counted twice:
sound, not tight. Identifiers are positional, `id` a `Finset (Fin pZ.p)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- How many of the sorted columns the scan takes: one is taken while the running sum `Val_curr`
plus its absolute value stays at most `Th` in every coordinate. -/
@[step_of PolyZonotope.outerApprox]
noncomputable def PolyZonotope.step_outerApproxCount (Th : Fin n → ℝ) :
    List (Fin n → ℝ) → (Fin n → ℝ) → ℕ
  | [], _ => 0
  | g :: gs, v =>
    if ∀ k, |g k| + v k ≤ Th k then
      1 + PolyZonotope.step_outerApproxCount Th gs (fun k => v k + |g k|)
    else 0


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- `outerApprox(pZ, tol, id)`. -/
noncomputable def PolyZonotope.outerApprox (pZ : PolyZonotope (Vec ℝ n)) (tol : ℝ)
    (S : Finset (Fin pZ.p)) : PolyZonotope (Vec ℝ n) :=
  -- `ii`: the dependent generators that depend on a factor outside `id`
  let dep : Fin pZ.h → Prop := fun i => ∃ k, k ∉ S ∧ 0 < pZ.E k i
  -- `ind_even`: the monomial is even in every factor, so it lies in `[0, 1]`
  let even : Fin pZ.h → Prop := fun i => ∀ k, pZ.E k i % 2 = 0
  -- the candidates `[G(:,ii), GI]`
  let cand : List (Fin pZ.h ⊕ Fin pZ.q) :=
    ((List.finRange pZ.h).filter fun i => decide (dep i)).map Sum.inl
      ++ (List.finRange pZ.q).map Sum.inr
  -- `GGI`, the even columns halved
  let GGI : Fin pZ.h ⊕ Fin pZ.q → Vec ℝ n
    | Sum.inl i => if even i then (1 / 2 : ℝ) • pZ.G i else pZ.G i
    | Sum.inr j => pZ.GI j
  -- `sort(sum(abs(GGI),1),'ascend')`
  let sorted : List (Fin pZ.h ⊕ Fin pZ.q) :=
    cand.mergeSort fun s t => decide ((∑ k, |GGI s k|) ≤ ∑ k, |GGI t k|)
  -- `Th = max(abs(GGI),[],2)*tol`
  let Th : Fin n → ℝ := fun k => tol * (cand.map fun t => |GGI t k|).foldr max 0
  -- `redCount`: the scan over the sorted columns
  let redCount : ℕ :=
    PolyZonotope.step_outerApproxCount Th (sorted.map fun t k => |GGI t k|) (fun _ => 0)
  -- `ii_red`
  let red : List (Fin pZ.h ⊕ Fin pZ.q) := sorted.take redCount
  -- `ii_red_G`, `ii_red_GI`: the removed dependent and the taken independent generators
  pZ.boxOut (fun i => Sum.inl i ∈ red) (fun j => Sum.inr j ∈ red)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
