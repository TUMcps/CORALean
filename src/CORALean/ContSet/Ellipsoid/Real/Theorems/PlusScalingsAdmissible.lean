import CORALean.ContSet.Ellipsoid.Real.Operations.Plus

/-!
# Kurzhanski and Varaiya's `l` names an admissible pair

`plus_outer` takes the two scalings and the inequality `1/s₁² + 1/s₂² ≤ 1`,
which is a two-dimensional set of admissible pairs. The classical family

  `Q(l) = (1 + 1/l) Q₁ + (1 + l) Q₂`,   `l > 0`,

is one curve through it: in generator form its scalings are `√(1+1/l)` and
`√(1+l)`, and this is the computation — one line — that they meet the bound
with *equality*, so `l` sweeps the boundary and nothing else. What lies inside
it is out of `l`'s reach, as is every pair with a negative scaling, which names
the same enclosure with a column of `G` flipped in sign.

A caller holding an `l` therefore discharges `plus_outer`'s three hypotheses
here, and loses nothing to the wider parametrisation.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The scalings `√(1+1/l)` and `√(1+l)` are non-zero and meet `plus_outer`'s
bound with equality, at every positive `l`. -/
theorem Ellipsoid.plus_scalings_admissible {l : ℝ} (hl : 0 < l) :
    Real.sqrt (1 + 1 / l) ≠ 0 ∧ Real.sqrt (1 + l) ≠ 0 ∧
      1 / Real.sqrt (1 + 1 / l) ^ 2
        + 1 / Real.sqrt (1 + l) ^ 2 = 1 := by -- --- PROOF ---
  have hlne : l ≠ 0 := ne_of_gt hl
  have hb2 : (0:ℝ) < 1 + l := by linarith
  have ha2 : (0:ℝ) < 1 + 1 / l := by
    have := one_div_pos.mpr hl
    linarith
  refine ⟨ne_of_gt (Real.sqrt_pos.mpr ha2), ne_of_gt (Real.sqrt_pos.mpr hb2), ?_⟩
  -- the squares undo the roots, leaving `1/(1+1/l) + 1/(1+l) = l/(l+1) + 1/(l+1)`
  rw [Real.sq_sqrt (le_of_lt ha2), Real.sq_sqrt (le_of_lt hb2)]
  field_simp
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
