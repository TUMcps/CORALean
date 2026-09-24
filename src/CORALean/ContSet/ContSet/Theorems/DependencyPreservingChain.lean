import CORALean.ContSet.ContSet.Definitions.DependencyPreserving

/-!
# [1, Lemma 5]: the whole loop preserves dependencies, not only one step

[1] reads its reachability algorithm as the post operator composed over every
time step, so the step's dependency preservation — [1, Lemma 4] — together with
[1, Lemma 2] gives the algorithm's. That induction is run here on the chain
itself: `e i` evaluates what the algorithm has computed after `i` steps from the
whole initial set, `R i` is what those same steps compute from a sub-parameterized
one, and the conclusion places `R N` inside `e N d` at every horizon `N`.

A chain and not an N-fold composition operator: `R` is what a loop returns, so
`hR` reads as the loop body — the shape `NonlinearSys.relinReach`'s own enclosure
theorems already have, and what an instance would have to supply anyway.

`hA` is [1]'s property (6) per step, and it is what carries step `i`'s inclusion
into step `i + 1`; without it the induction hypothesis meets `A i` and stops.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 5]: a chain started inside the parameterized set stays inside the
computed chain's own evaluation at that parameter, at every horizon. -/
theorem DependencyPreserving.chain {D α : Type} {A : ℕ → Set α → Set α} {e : ℕ → D → Set α}
    (hA : ∀ i, Monotone (A i)) (hstep : ∀ i, DependencyPreserving (A i) (e i) (e (i + 1)))
    {R : ℕ → Set α} (hR : ∀ i, R (i + 1) = A i (R i)) {d : D} (h0 : R 0 ⊆ e 0 d) :
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
