module

public import CORALean.ContSet.Polygon.Real.Operations.IsequalCora
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isequal_cora_counterexample (tol : ℝ) (h0 : 0 ≤ tol) (h2 : tol < 2) :
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
