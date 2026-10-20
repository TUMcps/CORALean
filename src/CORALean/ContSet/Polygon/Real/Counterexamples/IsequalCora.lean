module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CORA's `polygon/isequal` reports a polygon unequal to its own re-start

CORA's `@polygon/isequal.m` (l. 1-76) compares the boundary vertex lists (after
`removeCollinearPoints`, taken as given): every position `idx` in `V2` holding `V1(1,:)` is tried as
the start of a cyclic re-ordering. The loop (l. 64-71), `for i = 1:length(idx)`, re-orders from
`idx`, not `idx(i)`; MATLAB's colon takes the first element, so only the first position is tried.
For the boundary through the origin `O` twice, `V1 = (O, A, B, O, C, D)`, `V2 = (O, C, D, O, A, B)`
(`A = (1,1)`, `B = (1,-1)`, `C = (-1,-1)`, `D = (-1,1)`), the same boundary started at its fourth
vertex, `idx = [1 4]` and both passes re-order from `1`: `isequal` answers `false` for equal
polygons, for every tolerance below `2`. A wrong answer, not unsound. Read from the source, not run.

## Inputs
* `tol` – tolerance

## Hypotheses
* `h0` – `0 ≤ tol`
* `h2` – `tol < 2`

## Conclusion
* CORA's `isequal` calls a boundary and its re-start unequal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- CORA's `res` for `isequal(pgon1, pgon2, tol)`, from the vertex lists `V1`, `V2`. -/
noncomputable def Polygon.isequalCora (tol : ℝ) (V1 V2 : List (Vec ℝ 2)) : Bool :=
  -- l. 43: both empty -> `res = true`
  if V1 = [] ∧ V2 = [] then true
  -- l. 49: different numbers of vertices -> `res = false`
  else if V1.length ≠ V2.length then false
  else
    -- l. 56: `idx = find(all(withinTol(V1(1,:), V2, tol), 2))`, as 0-based positions
    let idx : List ℕ := (List.range V2.length).filter fun j =>
      (decide (|V1.head! 0 - V2[j]! 0| ≤ tol ∧ |V1.head! 1 - V2[j]! 1| ≤ tol))
    -- l. 59: `isempty(idx)` -> `res = false`
    if idx = [] then false
    else
      -- l. 64: `for i = 1:length(idx)`: the start is `idx`, which MATLAB's colon reads as `idx(1)`
      idx.any fun _ =>
        -- l. 66: `V2_ = [V2(idx:end, :); V2(1:idx-1, :)]`
        let V2_ := V2.drop idx.head! ++ V2.take idx.head!
        -- l. 68: `compareMatrices(V1, V2_, tol, 'equal', true)`
        (decide (List.Forall₂ (fun a b => |a 0 - b 0| ≤ tol ∧ |a 1 - b 1| ≤ tol) V1 V2_))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isequal_cora_counterexample (tol : ℝ) (h0 : 0 ≤ tol)
    (h2 : tol < 2) : -- --- CONCL ---
    let O : Vec ℝ 2 := ![0, 0]
    let A : Vec ℝ 2 := ![1, 1]
    let B : Vec ℝ 2 := ![1, -1]
    let C : Vec ℝ 2 := ![-1, -1]
    let D : Vec ℝ 2 := ![-1, 1]
    let V1 := [O, A, B, O, C, D]
    let V2 := [O, C, D, O, A, B]
    V2.rotate 3 = V1 ∧ V1.rotate 3 = V2 ∧
      Polygon.isequalCora tol V1 V2 = false := by -- --- PROOF ---
  intro O A B C D V1 V2
  refine ⟨rfl, rfl, ?_⟩
  have hl : ¬ List.Forall₂
      (fun a b : Vec ℝ 2 => |a 0 - b 0| ≤ tol ∧ |a 1 - b 1| ≤ tol) V1 V2 := by
    intro h
    simp only [V1, V2, List.forall₂_cons] at h
    have h1 := h.2.1.1
    norm_num [A, C] at h1
    linarith
  unfold Polygon.isequalCora
  rw [if_neg (by simp [V1]), if_neg (by simp [V1, V2])]
  dsimp only
  generalize hf : List.filter _ (List.range V2.length) = idx
  have h0' : idx.head! = 0 ∧ idx ≠ [] := by
    rw [← hf, show List.range V2.length = [0, 1, 2, 3, 4, 5] from rfl]
    simp [List.filter_cons, V1, V2, O, h0]
  rw [if_neg h0'.2, h0'.1]
  simpa using fun _ _ => hl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
