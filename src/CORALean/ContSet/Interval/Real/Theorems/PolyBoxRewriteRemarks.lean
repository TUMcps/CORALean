import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# The two rewritings of the remarks are identities

[1, Sec. 3 (remarks)]: the symbolic preprocessing rewrites Caprasse's
`-2x + 2txy - z + y²z = 0` into `(-2 + 2ty)x + (-1 + y²)z = 0`, where `x` and `z` occur once, and
6body's `5(b₁ - d₁) + 3(b₂ - d₂)(b₁ + d₁ - 2f₁) = 0` into
`b₁(5 + 3(b₂ - d₂)) + (-5 + 3b₂ - 3d₂)d₁ + 6(-b₂ + d₂)f₁ = 0`. Both are the same polynomial,
which a rewriting has to be; the CPU-time effects the remarks report are measurements.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.polyBox_rewrite_remarks :
    (∀ x y z t : ℝ,
      -2 * x + 2 * t * x * y - z + y ^ 2 * z = (-2 + 2 * t * y) * x + (-1 + y ^ 2) * z) ∧
    (∀ b₁ b₂ d₁ d₂ f₁ : ℝ, 5 * (b₁ - d₁) + 3 * (b₂ - d₂) * (b₁ + d₁ - 2 * f₁) =
      b₁ * (5 + 3 * (b₂ - d₂)) + (-5 + 3 * b₂ - 3 * d₂) * d₁ + 6 * (-b₂ + d₂) * f₁) :=
  ⟨fun _ _ _ _ => by ring, fun _ _ _ _ _ => by ring⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
