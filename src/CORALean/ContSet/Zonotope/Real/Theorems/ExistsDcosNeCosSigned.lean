module

public import CORALean.ContSet.Zonotope.Real.Operations.Dcos

@[expose] public section

/-!
# [1, Eq. (4)] is not the cosine it is said to be

[1] says (4) "computes the cosine of the angle between `sign(gᵢ(1))gᵢ` and `sign(gⱼ(1))gⱼ`".
It does not when exactly one first element is `0` and the other negative: `sign(gᵢ(1) gⱼ(1))`
is then `sign 0 = 1`, while `sign(gᵢ(1)) sign(gⱼ(1)) = -1`. For `gᵢ = (-1, 1)`, `gⱼ = (0, 1)` the
cosine of `(1, -1)` and `(0, 1)` is `-1/√2` and (4) gives `1/√2`.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The printed `dcos` differs from the cosine between the sign-aligned generators. -/
theorem Zonotope.exists_dcos_ne_cosSigned : -- --- CONCL ---
    ∃ gi gj : Vec ℝ 2,
    Zonotope.dcos gi gj ≠
      dotProduct ((if gi 0 < 0 then (-1 : ℝ) else 1) • gi) ((if gj 0 < 0 then (-1 : ℝ) else 1) • gj)
        / (‖(if gi 0 < 0 then (-1 : ℝ) else 1) • gi‖₂ * ‖(if gj 0 < 0 then (-1 : ℝ) else 1) • gj‖₂)
    := by -- --- PROOF ---
  -- `gᵢ = (-1, 1)`, `gⱼ = (0, 1)`: the printed value is `1/√2`, the cosine `-1/√2`
  refine ⟨![-1, 1], ![0, 1], ?_⟩
  simp [Zonotope.dcos, dotProduct, norm₂, Fin.sum_univ_two]
  have h : (0:ℝ) < √(1 + 1) := by positivity
  rw [neg_div, ← one_div]
  intro h2
  have := one_div_pos.mpr h
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
