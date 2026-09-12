import CORALean.ContDynamics.LinearSys.MatExp.ExactSecondOrder

/-!
# The diagonal parabola attains both of its bounds

[1, Lemma 3.1], the half that makes the enclosure *exact* rather than merely
sound: each of `quadTermLo`/`quadTermHi` is a value `γ` really takes on the
box, so no smaller interval encloses `γ` there.

`t ≠ 0` is what the vertex branch needs and all it is needed for: `γ (-1/t)` is
`-1/2` only where `-1/t` is a real point. At `t = 0` the enclosure is still
sound — see `quadTerm_between` — but the vertex branch's `-1/2` is then a gap.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


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
