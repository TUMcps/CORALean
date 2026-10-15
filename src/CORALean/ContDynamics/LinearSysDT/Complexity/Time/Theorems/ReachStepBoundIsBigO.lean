module

public import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Operations.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

/-!
# A step of `reach` is `O(n ^ 3)`

The one `O` statement in this directory, and it is a *slice*: `reachStepBound`
grows in three parameters — the dimension `n`, the order `o` and the input set's
generator count `hU` — and `IsBigO` takes a function of one argument along one
filter. So the composable claim is `reachCost_le`, an inequality in all three,
and this is what it reads as in `n` at fixed `o` and `hU`. Turning it round
costs a constant that `IsBigO` then discards, which is why the tree states the
inequality first and this second.

`n ^ 3` is the `mtimes`: `o * n` generators through an `n × n` matrix. The
`reduce` behind it is quadratic in `o * n + hU`, since `Cost.sort_le_mul_succ`
is all this proof reads of the sort — at fixed `o` that is only `n ^ 2`, so
neither the sort's shape nor a later tightening of it shows here.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The step bound against `C * n ^ 3`, in ℕ, with `C` written out: every term
loses its lower powers of `n` to `1 ≤ n` and its `hU` to `hU ≤ hU * n`, and the
sort enters as `Cost.sort_le_mul_succ` rather than as its definition. -/
theorem LinearSysDT.aux_reachStepBound_ops_le (n hU o : ℕ) (hn : 1 ≤ n) :
    (LinearSysDT.reachStepBound n hU o).ops
      ≤ (3 * (o + 1) + (2 + o + hU) + 6 * (o + hU) + ((o + hU) * (o + hU) + (o + hU))
          + (2 * (o + hU) + (2 + (o + hU)))) * n ^ 3 := by -- --- PROOF ---
  -- the three counts, unfolded as far as `Cost.sort`, whose shape stays opaque
  have hops : (LinearSysDT.reachStepBound n hU o).ops
      = (o * n + 1) * (2 * (n * n) + n) + (n + n * (1 + o * n + hU))
        + ((o * n + hU) * (4 * n + 2) + (Cost.sort (o * n + hU)).ops
            + (2 * (n * (o * n + hU)) + n * (1 + (o * n + hU) + n))) := rfl
  -- every power of `n` below the third is one, since `1 ≤ n`
  have hnn : n * n ≤ n ^ 3 := by
    calc n * n = n * n * 1 := by ring
      _ ≤ n * n * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 3 := by ring
  have hn3 : n ≤ n ^ 3 := le_trans (by calc n = n * 1 := by ring
    _ ≤ n * n := Nat.mul_le_mul_left _ hn) hnn
  -- `hU` is a constant, so it is bounded by `hU * n` and folds into the order
  have hH : o * n + hU ≤ (o + hU) * n := by
    calc o * n + hU ≤ o * n + hU * n := Nat.add_le_add_left (Nat.le_mul_of_pos_right hU hn) _
      _ = (o + hU) * n := by ring
  -- the `mtimes`: `o * n + 1` generators, each an `n × n` matrix-vector product and its writes
  have h1 : (o * n + 1) * (2 * (n * n) + n) ≤ 3 * (o + 1) * n ^ 3 := by
    calc (o * n + 1) * (2 * (n * n) + n)
        ≤ ((o + 1) * n) * (3 * (n * n)) := by
          refine Nat.mul_le_mul ?_ ?_
          · calc o * n + 1 ≤ o * n + n := Nat.add_le_add_left hn _
              _ = (o + 1) * n := by ring
          · nlinarith
      _ = 3 * (o + 1) * n ^ 3 := by ring
  -- the `plus`: the sum of the centers and the writes of its result
  have h2 : n + n * (1 + o * n + hU) ≤ (2 + o + hU) * n ^ 3 := by
    have a : n * (o * n) ≤ o * n ^ 3 := by
      calc n * (o * n) = o * (n * n) := by ring
        _ ≤ o * n ^ 3 := Nat.mul_le_mul_left _ hnn
    have b : n * hU ≤ hU * n ^ 3 := by
      calc n * hU = hU * n := by ring
        _ ≤ hU * n ^ 3 := Nat.mul_le_mul_left _ hn3
    have c : n * (1 + o * n + hU) = n + n * (o * n) + n * hU := by ring
    have d : (2 + o + hU) * n ^ 3 = 2 * n ^ 3 + o * n ^ 3 + hU * n ^ 3 := by ring
    omega
  -- the metric pass, the sort and the absorbed block, in that order
  have h3 : (o * n + hU) * (4 * n + 2) ≤ 6 * (o + hU) * n ^ 3 := by
    calc (o * n + hU) * (4 * n + 2)
        ≤ ((o + hU) * n) * (6 * n) := Nat.mul_le_mul hH (by omega)
      _ = 6 * (o + hU) * (n * n) := by ring
      _ ≤ 6 * (o + hU) * n ^ 3 := Nat.mul_le_mul_left _ hnn
  -- the sort, through its stated bound `k * (k + 1)` and not through its shape
  have h4 : (Cost.sort (o * n + hU)).ops
      ≤ ((o + hU) * (o + hU) + (o + hU)) * n ^ 3 := by
    calc (Cost.sort (o * n + hU)).ops
        ≤ (o * n + hU) * (o * n + hU + 1) := Cost.sort_le_mul_succ _
      _ = (o * n + hU) * (o * n + hU) + (o * n + hU) := by ring
      _ ≤ ((o + hU) * n) * ((o + hU) * n) + (o + hU) * n :=
          Nat.add_le_add (Nat.mul_le_mul hH hH) hH
      _ = (o + hU) * (o + hU) * (n * n) + (o + hU) * n := by ring
      _ ≤ (o + hU) * (o + hU) * n ^ 3 + (o + hU) * n ^ 3 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hnn) (Nat.mul_le_mul_left _ hn3)
      _ = ((o + hU) * (o + hU) + (o + hU)) * n ^ 3 := by ring
  -- `reduceBy`: the row sums and the writes of its result
  have h5 : 2 * (n * (o * n + hU)) + n * (1 + (o * n + hU) + n)
      ≤ (2 * (o + hU) + (2 + (o + hU))) * n ^ 3 := by
    have a : n * (o * n + hU) ≤ (o + hU) * n ^ 3 := by
      calc n * (o * n + hU) ≤ n * ((o + hU) * n) := Nat.mul_le_mul_left _ hH
        _ = (o + hU) * (n * n) := by ring
        _ ≤ (o + hU) * n ^ 3 := Nat.mul_le_mul_left _ hnn
    have c : n * (1 + (o * n + hU) + n) = n + n * (o * n + hU) + n * n := by ring
    have d : (2 * (o + hU) + (2 + (o + hU))) * n ^ 3
        = 2 * ((o + hU) * n ^ 3) + (2 * n ^ 3 + (o + hU) * n ^ 3) := by ring
    omega
  -- and the five bounds add up to the constant, times `n ^ 3`
  rw [hops]
  linarith [h1, h2, h3, h4, h5]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step of `reach` at `𝒵`, in the dimension alone: cubic, the `mtimes`
against `o * n` generators dominating. -/
theorem LinearSysDT.reachStepBound_isBigO (hU o : ℕ) :
    (fun n : ℕ => ((LinearSysDT.reachStepBound n hU o).ops : ℝ))
      =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ 3 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound
    ((3 * (o + 1) + (2 + o + hU) + 6 * (o + hU) + ((o + hU) * (o + hU) + (o + hU))
        + (2 * (o + hU) + (2 + (o + hU))) : ℕ) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast LinearSysDT.aux_reachStepBound_ops_le n hU o hn

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
