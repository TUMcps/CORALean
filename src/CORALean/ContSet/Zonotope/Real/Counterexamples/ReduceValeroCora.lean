module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Zonotope.valeroCora`: `reduce(Z,'valero',order)` takes the leftover of the wrong run

`priv_reduceValero.m` builds, for each of `ng = 2` candidate first generators `i`, a basis `Tr`
(Gram-Schmidt: the next column is the one with the largest residual) and keeps the basis `Trn` of
the largest `|det(Tr)|` (l. 45-74). The leftover generators `T` of the run are overwritten in every
run. After the loop `Tr = Trn` is the best run's basis (l. 75) but `T` is still the leftover of the
LAST run (`i = 2`), sorted by length and merged by `alpha = 1 + sum |Tr \ T(:,1:end-g+n)|`. When
the best run is the first, the generators that run 2 took into its basis and run 1 left over are
in neither `Tr`, `alpha` nor `T`: they are lost, and the result does not contain `Z`. `valero` is a
case of the public `reduce` (l. 160), not in the list of `reach`. Modelled for `n = 2`, center `0`,
generators in `ℤ²`, the result in `ℚ²`. Read from the source, not run.

# CORA's `reduce(Z,'valero',order)` loses a generator

`G = [0 -1 3 1; -1 1 -2 0]`, `order = 1.5` (`g = 3`): sorted by length `g3 = (3,-2), g2 = (-1,1),
g1 = (0,-1), g4 = (1,0)`. Run 1 picks `Tr = [g3, g1]` (`|det| = 3`, leftover `[g4, g2]`), run 2
`Tr = [g2, g3]` (`|det| = 1`, leftover `[g1, g4]`). `Trn` is run 1's, `T = [g1, g4]`, and `k = 1`
merges `g1`: `Zred = [(3,-2), (0,-2), (1,0)]`. `g2 = (-1,1)` is gone: in the direction `(-1,1)` the
support is `9` for `Z` and `8` for `Zred`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a point of `Z` is missing from CORA's reduced result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Insertion of the head into the sorted tail: `a` goes before the first `b` it may precede, so
with a non-strict `before` equal keys keep their order, as in MATLAB's `sort`. -/
def Zonotope.aux_insert {α : Type} (before : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if before a b then a :: b :: l else b :: aux_insert before a l

/-- Insertion sort, stable for a non-strict `before`. -/
def Zonotope.aux_sort {α : Type} (before : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => aux_insert before a (aux_sort before l)

/-- The determinant of two columns. -/
def Zonotope.aux_det (a b : ℤ × ℤ) : ℤ := a.1 * b.2 - a.2 * b.1

/-- The squared length. -/
def Zonotope.aux_normSq (a : ℤ × ℤ) : ℤ := a.1 ^ 2 + a.2 ^ 2

/-- One run `i` of the loop (l. 45-74) in `ℝ²`: the first column `T(:,i)`, then the column with
the largest residual (the rest sorted by `|det|` descending, stable); returns the basis and the
leftover `T` in the order MATLAB leaves it. -/
def Zonotope.aux_run (G : List (ℤ × ℤ)) (i : Nat) : (ℤ × ℤ) × (ℤ × ℤ) × List (ℤ × ℤ) :=
  let f := G.getD i (0, 0)
  let s := aux_sort (fun a b => decide (|aux_det f a| ≥ |aux_det f b|)) (G.eraseIdx i)
  (f, s.headD (0, 0), s.tail)

/-- `alpha_j = 1 + sum |(Tr \ g)_j|` over the merged columns, `Tr = [t1, t2]`. -/
def Zonotope.aux_alpha (t1 t2 : ℤ × ℤ) (M : List (ℤ × ℤ)) : ℚ × ℚ :=
  (1 + (M.map fun g => |(aux_det g t2 : ℚ) / aux_det t1 t2|).sum,
   1 + (M.map fun g => |(aux_det t1 g : ℚ) / aux_det t1 t2|).sum)


-- The model: CORA's code as printed, kept only to be refuted.
/-- The generators of `reduce(Z,'valero',order)` for `n = 2` with `g = order * n` and `ng = 2`:
`Tr` of the best run, `T` of the last. -/
def Zonotope.valeroCora (G : List (ℤ × ℤ)) (g : Nat) : List (ℚ × ℚ) :=
  let Gs := aux_sort (fun a b => decide (aux_normSq a ≥ aux_normSq b)) G   -- sort by length
  let r1 := aux_run Gs 0                                               -- i = 1
  let r2 := aux_run Gs 1                                               -- i = 2
  let best := if |aux_det r2.1 r2.2.1| > |aux_det r1.1 r1.2.1| then r2 else r1   -- volTn > volF
  let T := aux_sort (fun a b => decide (aux_normSq a ≤ aux_normSq b)) r2.2.2  -- T of the LAST run
  let k := T.length + 2 - g                                            -- end - g + n
  let a := aux_alpha best.1 best.2.1 (T.take k)
  [(a.1 * best.1.1, a.1 * best.1.2), (a.2 * best.2.1.1, a.2 * best.2.1.2)]
    ++ (T.drop k).map fun v => ((v.1 : ℚ), (v.2 : ℚ))

/-- The zonotope with center `0` and generators `G`: the combinations with coefficients in
`[-1, 1]`. -/
def Zonotope.aux_zonotope (G : List (ℚ × ℚ)) : Set (ℚ × ℚ) :=
  {z | ∃ s : List ℚ, s.length = G.length ∧ (∀ x ∈ s, |x| ≤ 1) ∧
    z = ((List.zipWith (fun a g => (a * g.1, a * g.2)) s G).map Prod.fst |>.sum,
         (List.zipWith (fun a g => (a * g.1, a * g.2)) s G).map Prod.snd |>.sum)}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result is `[(3,-2), (0,-2), (1,0)]`; `(-5, 4)` is a point of `Z` (support `9` in the
direction `(-1,1)`) and not of the result (support `8`). -/
theorem Zonotope.valeroCora_counterexample :
    valeroCora [(0, -1), (-1, 1), (3, -2), (1, 0)] 3 = [(3, -2), (0, -2), (1, 0)] ∧
      ((-5 : ℚ), (4 : ℚ)) ∈ aux_zonotope [(0, -1), (-1, 1), (3, -2), (1, 0)] ∧
      ((-5 : ℚ), (4 : ℚ)) ∉ aux_zonotope [(3, -2), (0, -2), (1, 0)] := by -- --- PROOF ---
  refine ⟨?_, ⟨[-1, 1, -1, -1], by simp, ?_, by norm_num [List.zipWith]⟩, ?_⟩
  · simp (config := {decide := true}) [valeroCora, aux_run, aux_sort, aux_insert, aux_det,
      aux_normSq, aux_alpha]
    norm_num
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h <;> subst h <;> norm_num
  · rintro ⟨s, hlen, hs, hz⟩
    match s, hlen, hs, hz with
    | [a, b, c], _, hs, hz =>
      simp [List.zipWith] at hz
      have ha := abs_le.mp (hs a (by simp))
      have hc := abs_le.mp (hs c (by simp))
      obtain ⟨h1, _⟩ := hz
      linarith [ha.1, ha.2, hc.1, hc.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
