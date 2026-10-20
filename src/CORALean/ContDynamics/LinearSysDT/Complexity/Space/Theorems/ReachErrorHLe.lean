module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Theorems.ReduceBoxH

@[expose] public section

/-!
# `LinearSysDT.reachError` does not bound its own generator count

`reach_order_le` bounds the generator count of `sys.reach` by `o * n` for *every* `k`, the last
step always ending in a `reduce`. `reachError` reduces nothing — it is one box per step, carried
forward and added to — so what bounds it is `k * n`: linear in the steps taken. The proof mirrors
its recursion: `mtimes_h` and `plus_h` cost the running total nothing, and `reduceBox_h` adds at
most `n` per step. Unlike `reach_order_le`, no `k`-independent bound holds in general: past
`k = o` steps the proved bound exceeds every bound `reach`'s own count can reach, the sharp form
of the worry `ReachInner.lean` records.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Conclusion
* the error set has at most `k * n` generators
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `reach` owes after `k` steps has at most `k * n` generators — growing
in the number of steps taken, unlike `reach_order_le`'s `o * n`, which does
not. -/
theorem LinearSysDT.reachError_h_le (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).h ≤ k * n := by -- --- PROOF ---
  induction k with
  | zero =>
    -- the origin has no generators
    show (Zonotope.ofPoint (0 : Vec ℝ n)).h ≤ 0 * n
    simp [Zonotope.ofPoint]
  | succ k ih =>
    have herr : sys.reachError ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
        = (Zonotope.mtimes sys.A (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus
            (Zonotope.reduceBox
              ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) o) :=
      rfl
    have hbox : (Zonotope.reduceBox
        ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) o).h ≤ n := by
      rw [Zonotope.reduceBox_h]; split_ifs <;> omega
    calc (sys.reachError ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h
        = (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).h
            + (Zonotope.reduceBox
                ((Zonotope.mtimes sys.A
                  (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) o).h := by
          rw [herr, Zonotope.plus_h, Zonotope.mtimes_h]
      _ ≤ k * n + n := by omega
      _ = (k + 1) * n := by ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
