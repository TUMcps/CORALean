import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith

/-!
# One Lagrange point for all coordinates misses the linearization error

[1, Eq. 10], [1, Eq. 11] and [1, Eq. 20] write the remainder of the linearization as
`½ σ`, `σᵢ = νᵀ H⁽ⁱ⁾(ξ) ν`, `ξ ∈ R^z`, `ν ∈ R^z_Δ`, with one `ξ` shared by every coordinate
`i`. The mean value theorem of [1, Eq. 8] gives each row its own `ξ⁽ⁱ⁾`; one shared need not exist.

Two differential variables and no algebraic ones or inputs (an ordinary system, which the
paper covers as a special case; for [1, Eq. 11] the same `p`, `q` serve as the constraints
`g = (p(x₁) - y₁, q(x₁) - y₂)`, `F = -I`, whose remainder is the same pair):
`f(x) = (p(x₁), q(x₁))`, `p(x) = x²/2 - x³/3 + x⁴/12`, `q(x) = x⁴/12`, so
`p'' = (1 - x)²`, `q'' = x²` (the first four conjuncts certify these derivatives), and the
Hessians are `diag(p''(ξ₁), 0)`, `diag(q''(ξ₁), 0)`. Take `R^z = [-½, 1]²`, the
linearization point `z* = 0` inside it, and `z = (1, 0)`. Then `f(z*) = 0`, the Jacobian
at `z*` is `0`, and the remainder is `f(z) = (1/4, 1/12)`. The shared-`ξ` set holds it only
if `½ ν₁²(1 - ξ₁)² = 1/4` and `½ ν₁² ξ₁² = 1/12` for some `ξ₁, ν₁ ∈ [-½, 1]` (`R^z_Δ = R^z`
here), which forces `(1 - ξ₁)² = 3 ξ₁²`, so `2ξ₁² + 2ξ₁ - 1 = 0`, while `ν₁² ≤ 1` forces
`(1 - ξ₁)² ≥ ½`, so `ξ₁ ≤ ⅓`; the quadratic is negative on `[-½, ⅓]`. Per row the points
exist, `ξ⁽¹⁾ = 1 - 1/√2`, `ξ⁽²⁾ = 1/√6`.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 10]: `p'' = (1 - x)²`, `q'' = x²`, and the remainder `(p(1), q(1)) = (1/4, 1/12)`
of `f = (p(x₁), q(x₁))` at `z* = 0`, `z = (1, 0)` is not `½ (ν₁² p''(ξ₁), ν₁² q''(ξ₁))` for
any one `ξ₁` and `ν₁` in `[-½, 1]`. -/
theorem NonlinDASys.shared_lagrange_point_counterexample :
    (∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 12)
      (x - x ^ 2 + x ^ 3 / 3) x) ∧
    (∀ x : ℝ, HasDerivAt (fun x : ℝ => x - x ^ 2 + x ^ 3 / 3) ((1 - x) ^ 2) x) ∧
    (∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 4 / 12) (x ^ 3 / 3) x) ∧
    (∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 3 / 3) (x ^ 2) x) ∧
    ¬ ∃ ξ ∈ Icc (-1 / 2 : ℝ) 1, ∃ ν ∈ Icc (-1 / 2 : ℝ) 1,
      (1 : ℝ) ^ 2 / 2 - 1 ^ 3 / 3 + 1 ^ 4 / 12 = 1 / 2 * (ν * (1 - ξ) ^ 2 * ν) ∧
      (1 : ℝ) ^ 4 / 12 = 1 / 2 * (ν * ξ ^ 2 * ν) := by -- --- PROOF ---
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, ?_⟩
  -- the four derivatives, each a polynomial differentiated term by term
  · exact ((((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_pow 3 x).div_const 3)).add
      ((hasDerivAt_pow 4 x).div_const 12)).congr_deriv (by norm_num; ring)
  · exact (((hasDerivAt_id x).sub (hasDerivAt_pow 2 x)).add
      ((hasDerivAt_pow 3 x).div_const 3)).congr_deriv (by norm_num; ring)
  · exact ((hasDerivAt_pow 4 x).div_const 12).congr_deriv (by norm_num; ring)
  · exact ((hasDerivAt_pow 3 x).div_const 3).congr_deriv (by norm_num)
  -- no shared `ξ`: the two equations force `2ξ² + 2ξ - 1 = 0` with `ξ ≤ ⅓`
  · rintro ⟨ξ, ⟨hξ0, -⟩, ν, ⟨hν0, hν1⟩, h1, h2⟩
    have hs : ν * ν ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hν1) (by linarith : (0:ℝ) ≤ 1 + ν)]
    have e1 : ν * ν * (1 - ξ) ^ 2 = 1 / 2 := by linear_combination (-2) * h1
    have e2 : ν * ν * ξ ^ 2 = 1 / 6 := by linear_combination (-2) * h2
    have hpos : ν * ν ≠ 0 := fun h0 => by rw [h0] at e2; norm_num at e2
    -- the ratio of the two equations
    have hq : (1 - ξ) ^ 2 = 3 * ξ ^ 2 := by
      have h3 : ν * ν * ((1 - ξ) ^ 2 - 3 * ξ ^ 2) = 0 := by linear_combination e1 - 3 * e2
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hpos
      · linarith
    -- `ν² ≤ 1` keeps `(1 - ξ)²` at least `½`, so `ξ ≤ ⅓`
    have hge : 1 / 2 ≤ (1 - ξ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hs) (sq_nonneg (1 - ξ))]
    have hξ3 : ξ ≤ 1 / 3 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ξ + 1 / 2) (by linarith : (0:ℝ) ≤ 1 / 3 - ξ)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
