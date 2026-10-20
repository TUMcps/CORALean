module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxError
public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrderLoop
public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxErrorEqZero

@[expose] public section

/-!
# What `Alg. 3` returns is inside the budget it searched for

The soundness of [1, Alg. 3] as written here: the order it settles on costs an
`ε_S([t_i,t_{i+1}])` inside eq. (13)'s share of what is left of the `ε_S` budget, and the second
component is eq. (12)'s accumulation. The loop's invariant is that the order in hand is
admissible, so the search needs a starting point that already is — and has one: at the order
`Z.h` no generator is dropped, `reduceBox` is the origin and `err(·)` of the origin is `0`. That
is what `0 < n` and a non-negative share buy. Nothing asks the check's converse, so a check that
gives up early stops the search sooner and never lets a wider reduction through.

## Inputs
* `le` – decidable comparison on reals
* `Z` – zonotope
* `εSmax` – total set-error budget
* `εSacc` – error already accumulated
* `tf` – final time
* `ti` – current time
* `Δt` – time step

## Hypotheses
* `hle` – comparison implies the real order
* `hn` – dimension positive
* `hεSi` – error share nonnegative

## Conclusion
* order stays within the share and the accumulated error is updated

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 3-7 keep an admissible order admissible: every decrement the loop
takes is one the check cleared, and every exit hands back what it came in
with. -/
theorem aux_adaptSetOrderLoop_le {le : ℝ → ℝ → Bool} (hle : ∀ a b, le a b = true → a ≤ b)
    (Z : Zonotope (Vec ℝ n)) {εSi : ℝ} :
    ∀ (k Φset : ℕ), Z.reduceBoxError Φset ≤ εSi →
      Z.reduceBoxError (Zonotope.adaptSetOrderLoop le Z εSi Φset k) ≤ εSi := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro Φset h; rw [Zonotope.adaptSetOrderLoop]; exact h
  | succ k ih =>
    intro Φset h
    match Φset with
    | 0 => rw [Zonotope.adaptSetOrderLoop]; exact h
    | Φ + 1 =>
      rw [Zonotope.adaptSetOrderLoop]
      split
      -- the check cleared one order down, so the loop may carry the invariant there
      · rename_i hc
        exact ih _ (hle _ _ hc)
      · exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3]: the order it settles on is inside eq. (13)'s share of the
`ε_S` budget, and the error it accumulates is eq. (12)'s. -/
theorem Zonotope.adaptSetOrder_budget {le : ℝ → ℝ → Bool} (hle : ∀ a b, le a b = true → a ≤ b)
    (Z : Zonotope (Vec ℝ n)) {εSmax εSacc tf ti Δt : ℝ} (hn : 0 < n)
    (hεSi : 0 ≤ (εSmax - εSacc) / (tf - ti) * Δt) : -- --- CONCL ---
    Z.reduceBoxError (Z.adaptSetOrder le εSmax εSacc tf ti Δt).1
        ≤ (εSmax - εSacc) / (tf - ti) * Δt
      ∧ (Z.adaptSetOrder le εSmax εSacc tf ti Δt).2 = εSacc
        + Z.reduceBoxError (Z.adaptSetOrder le εSmax εSacc tf ti Δt).1 := by -- --- PROOF ---
  -- `param(PR)` drops no generator, so the loop starts admissible
  have hstart : Z.reduceBoxError Z.h ≤ (εSmax - εSacc) / (tf - ti) * Δt := by
    rw [Zonotope.reduceBoxError_eq_zero Z (Nat.le_mul_of_pos_right _ hn)]
    exact hεSi
  exact ⟨aux_adaptSetOrderLoop_le hle Z _ _ hstart, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
