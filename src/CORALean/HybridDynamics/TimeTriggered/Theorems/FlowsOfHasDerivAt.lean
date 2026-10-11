import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

/-!
# A curve with a derivative on a closed interval is a continuous successor

[1, Def. 4] asks for a differentiable `g : [0, t] → X` whose value and derivative lie in the
invariant and the flow on `(0, t)`. A curve that has a two-sided derivative at every point of
`[0, t]`, as the solutions of an ODE do, is one when its derivative lies in the flow inside.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {M X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A curve with derivative `v` on `[0, t]` is a continuous successor of its start, [1, Def. 4]. -/
theorem DiffInclAutomaton.flows_of_hasDerivAt {H : DiffInclAutomaton M X} {m : M} {y v : ℝ → X}
    {t : ℝ} (ht : 0 < t) (hy : ∀ u ∈ Icc 0 t, HasDerivAt y (v u) u)
    (hflow : ∀ u ∈ Ioo 0 t, v u ∈ H.flow m (y u)) (hinv : ∀ u ∈ Ioo 0 t, y u ∈ H.inv m) :
    H.Flows m (y 0) t (y t) :=
  ⟨ht, y, fun u hu => (hy u hu).differentiableAt.differentiableWithinAt, rfl, rfl,
    fun u hu => ⟨hinv u hu, by rw [(hy u (Ioo_subset_Icc_self hu)).deriv]; exact hflow u hu⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
