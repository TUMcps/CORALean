module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# A continuous-time system paired with an input set anywhere

`LinearSys.WithInput` without `0 ∈ U`: [1, Eq. 4]'s case, the input set taken
apart into a constant `ũ` and a remainder `Ũ` holding the origin before any
window is computed. The split is the representation's, by `Recenter`, so no
field here names it; `Reach LinearSys.WithInputSplit` asks the representation
for `Recenter` and `OfPoint` instead. `WithInput` stays for representations
without a center, where `0 ∈ U` is the hypothesis [2, Prop. 4]'s proof takes.

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
* [2] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A `LinearSys` paired with the input set every run draws from, wherever it
sits. -/
structure LinearSys.WithInputSplit (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : LinearSys 𝕋 n
  U : S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
