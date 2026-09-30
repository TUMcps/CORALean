import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
import CORALean.ContSet.Zonotope.Real.Complexity.Mtimes
import CORALean.ContSet.Zonotope.Real.Complexity.Plus
import CORALean.ContSet.Zonotope.Real.Complexity.ReduceBox

/-!
# `LinearSysDT.reachError` does not bound its own generator count

`reach_order_le` bounds `(sys.reach (S := 𝒵) o ho R₀ U (k + 1)).h` by `o * n`
for *every* `k`, the last step always ending in a `reduce`. `reachError`
reduces nothing — it is one box per step, carried forward and added to — so
what bounds it is `k * n`: linear in the steps taken, not a constant the run
never crosses.

The proof mirrors `reachError`'s own recursion: `mtimes_h` and `plus_h` cost
the running total nothing, and `reduceBox_h` adds at most `n` per step. Its
`if` can take either branch, so a system where `U` has no generators and `R₀`
is already at order `o` pays nothing at all — this is the shape of the worst
case, not a guarantee it is met. But unlike `reach_order_le`, no
`k`-independent bound holds in general, so the *proved* bound is the one that
grows: past `k = o` steps it already exceeds every bound `reach`'s own count
can ever reach, which is the sharp form of the worry `ReachInner.lean` records.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


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
    (sys.reachError o ho R₀ U k).h ≤ k * n := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSysDT.reachError, Zonotope.ofPoint]
  | succ k ih =>
    have herr : sys.reachError o ho R₀ U (k + 1)
        = (Zonotope.mtimes sys.A (sys.reachError o ho R₀ U k)).plus
            (Zonotope.reduceBox
              ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) o) :=
      rfl
    have hbox : (Zonotope.reduceBox
        ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) o).h ≤ n := by
      rw [Zonotope.reduceBox_h]; split_ifs <;> omega
    calc (sys.reachError o ho R₀ U (k + 1)).h
        = (sys.reachError o ho R₀ U k).h
            + (Zonotope.reduceBox
                ((Zonotope.mtimes sys.A
                  (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) o).h := by
          rw [herr, Zonotope.plus_h, Zonotope.mtimes_h]
      _ ≤ k * n + n := by omega
      _ = (k + 1) * n := by ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
