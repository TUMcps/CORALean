import CORALean.ContDynamics.LinearSys.MatExp.Operations.OneParamF
import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Div

/-!
# `MatExp.expmOneParam`

The matrix zonotope `K(r)` of [1, Thm. 1], enclosing the Taylor polynomial
`Σ_{i=0}^η (C + βG)ⁱ rⁱ/i!` of the matrix exponential over `β ∈ [-1, 1]`: generator `l = 1 … η` is
`G_K^{(l)} = Σ_{i=l}^η F_i^{(l)} rⁱ/i!`, halved for even `l`, and the centre is
`C_K = Σ_{l=0}^η D_l rˡ/l! + Σ_{l=1}^{⌊η/2⌋} G_K^{(2l)}`. CORA's `@matZonotope/expmOneParam`.
Generator `j` of the structure is `G_K^{(j+1)}`.

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". In Proc. of the American Control
      Conference, pp. 3559-3566, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def MatExp.expmOneParam (C G : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Zonotope (Mat ℝ n n) :=
  let D := MatExp.oneParamD C  -- `D_i`
  let F := MatExp.oneParamF C G  -- `F_i^{(l)}`
  let G_K : ℕ → Mat ℝ n n := fun l =>
    if Odd l then ∑ i ∈ Finset.Icc l η, (r ^ i / i.factorial) • F i l
    else (1 / 2 : ℝ) • ∑ i ∈ Finset.Icc l η, (r ^ i / i.factorial) • F i l  -- `G_K^{(l)}`
  let C_K := ∑ l ∈ Finset.range (η + 1), (r ^ l / l.factorial) • D l +
    ∑ l ∈ Finset.Icc 1 (η / 2), G_K (2 * l)  -- `C_K`
  ⟨η, C_K, fun j => G_K (j.val + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
