module

public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `HPolytope.minkDiff1DCora`: CORA's one-dimensional polytope `minkDiff`

`@polytope/minkDiff.m` sends two one-dimensional polytopes to `aux_minkDiff_1D` (l. 78-81,
146-176). It compacts both operands (l. 155, 161), returns the fullspace for a fullspace minuend
or an empty subtrahend (l. 157-165), errors on equality constraints (l. 167-171), and otherwise
returns `polytope(P_.A_.val, P_.b_.val - S_.b_.val)` (l. 174), on the comment "both A matrices are
normalized in minHRep". That subtraction pairs the minuend's rows with the subtrahend's by
position. `priv_compact_1D` ([2], l. 77-89) leaves two rows `[1; -1]` only for a set bounded on both
sides; a subtrahend bounded on one side keeps the single row `1` or `-1`, and MATLAB broadcasts
its one offset over both rows of the minuend, whatever that row's direction.

The compacted operands `P_`, `S_` are the arguments; the compaction is `priv_compact_1D`'s, not
modelled. `representsa_` reads as exact. MATLAB's `-` broadcasts a one-row operand, subtracts
equal lengths entrywise and errors otherwise (`none`). Read from the source, not run.

# CORA's 1-D polytope `minkDiff` with a one-sided subtrahend is not inner

The minuend `P = [-1, 1]` compacts to the rows `x ≤ 1`, `-x ≤ 1`; the subtrahend `S = {x ≤ 0}`
compacts to its single row `x ≤ 0` (`priv_compact_1D`, l. 77-89: `b = [0; min([])] = 0`, one
inequality, `A = 1`). `HPolytope.minkDiff1DCora` subtracts the offset `0` from both rows of the
minuend and returns `[-1, 1]` again, while `P ⊖ S` is empty: `S` is unbounded below and `P` is
not. So `0` is in CORA's result although `0 + (-2) ∉ P`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's 1-D difference contains `0` although `P ⊖ S` is empty

## References

* [1] `contSet/@polytope/minkDiff.m`, CORA, ll. 77-81, 146-176.
* [2] `contSet/@polytope/private/priv_compact_1D.m`, CORA, ll. 73-110.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- [1]'s `aux_minkDiff_1D` at the compacted operands `P_` and `S_`; `none` is an error. -/
noncomputable def HPolytope.minkDiff1DCora (P_ S_ : HPolytope (Vec ℝ 1)) :
    Option (HPolytope (Vec ℝ 1)) :=
  open Classical in
  -- l. 157-159: `if representsa_(P_,'fullspace',0)`, `P_out = polytope.Inf(n)`
  if P_.construct = Set.univ then some (HPolytope.fullspace _)
  -- l. 163-165: `if representsa_(S_,'emptySet',1e-10)`, `P_out = fullspace(n)`
  else if S_.construct = ∅ then some (HPolytope.fullspace _)
  -- l. 167-171: equality constraints, `CORA:notSupported`
  else if P_.me ≠ 0 ∨ S_.me ≠ 0 then none
  else
    -- l. 174: `P_.b_.val - S_.b_.val`, broadcast, entrywise, or an error
    let b : Option (Fin P_.m → ℝ) :=
      if h₁ : S_.m = 1 then some fun i => P_.b i - S_.b ⟨0, by omega⟩
      else if h : S_.m = P_.m then some fun i => P_.b i - S_.b (i.cast h.symm)
      else none
    -- l. 174: `P_out = polytope(P_.A_.val, ...)`
    b.map fun b => ⟨P_.m, P_.A, b, 0, Fin.elim0, Fin.elim0⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minkDiff1DCora_counterexample : -- --- CONCL ---
    let P_ : HPolytope (Vec ℝ 1) :=
      ⟨2, ![LinearMap.proj 0, -LinearMap.proj 0], ![1, 1], 0, Fin.elim0, Fin.elim0⟩
    let S_ : HPolytope (Vec ℝ 1) := ⟨1, ![LinearMap.proj 0], ![0], 0, Fin.elim0, Fin.elim0⟩
    ∃ Q, P_.minkDiff1DCora S_ = some Q ∧ (0 : Vec ℝ 1) ∈ Q.construct ∧
      minkowskiDiff P_.construct S_.construct = ∅ := by -- --- PROOF ---
  intro P_ S_
  -- `2 ∉ P_`, `0 ∈ S_`: no early return
  have hP : P_.construct ≠ Set.univ := fun h => by
    have h2 : (fun _ => 2 : Vec ℝ 1) ∈ P_.construct := h ▸ Set.mem_univ _
    have := h2.1 (show Fin 2 from 0)
    simp [P_] at this
  have hS : S_.construct ≠ ∅ := fun h => by
    have h0 : (0 : Vec ℝ 1) ∈ S_.construct :=
      ⟨fun i => by fin_cases i; simp [S_], fun i => i.elim0⟩
    rw [h] at h0
    exact h0
  -- CORA's result: both rows of `P_` keep their direction, offsets `1 - 0`
  refine ⟨⟨2, P_.A, fun i => P_.b i - S_.b 0, 0, Fin.elim0, Fin.elim0⟩, ?_, ?_, ?_⟩
  · simp [HPolytope.minkDiff1DCora, hP, hS, P_, S_]
  · refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i <;> simp [P_, S_]
  · -- `x + min 0 (-2 - x)` lies below `-1` for every `x`: the difference is empty
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hy : (fun _ => min 0 (-2 - x 0) : Vec ℝ 1) ∈ S_.construct := by
      refine ⟨fun i => ?_, fun i => i.elim0⟩
      fin_cases i
      simp [S_]
    have h := (hx _ hy).1 (show Fin 2 from 1)
    simp [P_] at h
    have := min_le_right (0 : ℝ) (-2 - x 0)
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
