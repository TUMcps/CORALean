module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Polygon.isequalCora`: `polygon/isequal` as CORA's code computes it

CORA's `@polygon/isequal.m` (l. 1-76) compares the boundary vertex lists of two polygons
(after `removeCollinearPoints`, taken here as given): equal numbers of vertices, then every
position `idx` in `V2` that holds `V1(1,:)` is tried as the start of a cyclic re-ordering of `V2`,
and the lists are compared in order. The loop (l. 64-71) reads

```
for i = 1:length(idx)
    V2_ = [V2(idx:end, :); V2(1:idx-1, :)];
```

with `idx`, not `idx(i)`. MATLAB's colon operator takes the first element of a vector operand,
so every pass re-orders `V2` from `idx(1)`. A boundary that visits one point twice has several
such positions, and only the first is ever tried. The lists are `List`s of vertices (rows of
`V1`, `V2`); `withinTol(a,b,tol)` is its absolute branch `|a - b| <= tol` (the relative branch is
only wider); `compareMatrices(..., tol, 'equal', true)` with equal sizes is `all(withinTol(…))`.
Read from the source, not run.

# CORA's `polygon/isequal` reports a polygon unequal to its own re-start

Take the boundary that runs through the origin `O` twice, once round each of two triangles
touching at `O`: `V1 = (O, A, B, O, C, D)` with `A = (1,1)`, `B = (1,-1)`, `C = (-1,-1)`,
`D = (-1,1)`, and `V2 = (O, C, D, O, A, B)`, the same closed boundary started at its fourth
vertex (`isequal.m` is written for this: "vertices have to be in order, but start of list can
vary"). `V1(1,:)` occurs in `V2` at the positions `idx = [1 4]`. The loop `for i = 1:length(idx)`
re-orders `V2` from `idx` read as `idx(1) = 1` in both passes, which is `V2` itself, and `V2` is
not `V1` (second vertex `C ≠ A`). So `isequal` answers `false` for equal polygons, for every
tolerance below `2`. The right start `idx(2) = 4` would give `V1`. A wrong answer, not unsound.
Read from the source, not run; whether MATLAB's `polyshape` keeps such a pinched boundary as
one loop in the order given is not checked.
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
    (h2 : tol < 2) : -- --- STMT ---
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
