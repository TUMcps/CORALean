module

public import CORALean.ContSet.ContSet.Definitions.IsDependencyPreserving
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# [1, Lemma 5]: the whole loop preserves dependencies, not only one step

[1] reads its reachability algorithm as the post operator composed over every time step, so the
step's dependency preservation — [1, Lemma 4] — with [1, Lemma 2] gives the algorithm's. That
induction is run here on the chain itself: `e i` evaluates what the algorithm has computed after `i`
steps from the whole initial set, `R i` is what the same steps compute from a sub-parameterized one,
and `R N` lies inside `e N d` at every horizon `N`. A chain and not an N-fold composition operator:
`hR` reads as the loop body, the shape `NonlinearSys.relinReach`'s own enclosure theorems already
have. `hA` is [1]'s property (6) per step; it carries step `i`'s inclusion into step `i + 1`.

## Inputs
* `D` – parameter domain
* `α` – set type
* `A` – operation per step
* `e` – evaluation function per step
* `R` – chain of sets
* `d` – parameter value

## Hypotheses
* `hA` – each operation monotone
* `hstep` – each step preserves dependencies
* `hR` – chain follows the operations
* `h0` – start lies in `e 0 d`

## Conclusion
* every chain element lies in the evaluation at `d`

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 5]: a chain started inside the parameterized set stays inside the
computed chain's own evaluation at that parameter, at every horizon. -/
theorem IsDependencyPreserving.chain {D α : Type} {A : ℕ → Set α → Set α} {e : ℕ → D → Set α}
    (hA : ∀ i, Monotone (A i)) (hstep : ∀ i, IsDependencyPreserving (A i) (e i) (e (i + 1)))
    {R : ℕ → Set α} (hR : ∀ i, R (i + 1) = A i (R i)) {d : D} (h0 : R 0 ⊆ e 0 d) : -- --- CONCL ---
    ∀ N, R N ⊆ e N d := by -- --- PROOF ---
  intro N
  induction N with
  | zero => exact h0
  | succ n ih =>
    rw [hR n]
    -- step `n` grows the horizon-`n` inclusion, and its dependency preservation lands it
    intro x hx
    exact hstep n d (hA n ih hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
