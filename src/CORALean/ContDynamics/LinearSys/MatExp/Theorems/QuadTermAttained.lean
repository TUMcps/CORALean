module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHi
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLo
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# The diagonal parabola attains both of its bounds

[1, Prop. 4], the half that makes the enclosure *exact* rather than merely
sound: each of `quadTermLo`/`quadTermHi` is a value `γ` really takes on the
box, so no smaller interval encloses `γ` there.

`t ≠ 0` is what the vertex branch needs and all it is needed for: `γ (-1/t)` is
`-1/2` only where `-1/t` is a real point. At `t = 0` the enclosure is still
sound — see `quadTerm_between` — but the vertex branch's `-1/2` is then a gap.

## Inputs
* `t` – time
* `a` – box lower end
* `b` – box upper end

## Hypotheses
* `hab` – box nonempty
* `ht` – time nonzero

## Conclusion
* both bounds of the parabola are attained inside the box

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both bounds of the parabola over `[a, b]` are attained inside `[a, b]`. -/
theorem MatExp.quadTerm_attained {t a b : ℝ} (hab : a ≤ b) (ht : t ≠ 0) :
    (∃ x, a ≤ x ∧ x ≤ b ∧ MatExp.quadTerm t x = MatExp.quadTermLo t a b) ∧
      (∃ x, a ≤ x ∧ x ≤ b ∧ MatExp.quadTerm t x = MatExp.quadTermHi t a b) := by -- --- PROOF ---
  constructor
  · rw [MatExp.quadTermLo]
    split
    · -- the box straddles the vertex, which is where `-1/2` is taken
      rename_i hv
      refine ⟨-1 / t, hv.1, hv.2, ?_⟩
      rw [MatExp.quadTerm]
      field_simp
      ring
    · -- otherwise the minimum is whichever endpoint `min` picked
      rcases le_total (MatExp.quadTerm t a) (MatExp.quadTerm t b) with h | h
      · exact ⟨a, le_rfl, hab, (min_eq_left h).symm⟩
      · exact ⟨b, hab, le_rfl, (min_eq_right h).symm⟩
  · -- the maximum is always at an endpoint
    rw [MatExp.quadTermHi]
    rcases le_total (MatExp.quadTerm t a) (MatExp.quadTerm t b) with h | h
    · exact ⟨b, hab, le_rfl, (max_eq_right h).symm⟩
    · exact ⟨a, le_rfl, hab, (max_eq_left h).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
