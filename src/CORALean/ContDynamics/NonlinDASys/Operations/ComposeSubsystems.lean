import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

/-!
# `NonlinDASys.composeSubsystems`

[1, Eq. 15], and the combination of the partial Lagrange remainders of [1, Sec. V-B]: the sets
`R⁽ⁱ⁾(τ_k)` of the `n_s` subsystems, each mapped to the states of the full system by its
matrix `Φ⁽ⁱ⁾`, joined into the set of the complete system. [1] writes the join as the Cartesian
product `Φ⁽¹⁾R⁽¹⁾(τ_k) × ... × Φ⁽ⁿˢ⁾R⁽ⁿˢ⁾(τ_k)`, but each `Φ⁽ⁱ⁾R⁽ⁱ⁾` already lies in the
states of the full system, whose product would have dimension `n_s n`; the join meant is the
Minkowski sum `Φ⁽¹⁾R⁽¹⁾ ⊕ ... ⊕ Φ⁽ⁿˢ⁾R⁽ⁿˢ⁾`, which for the `Φ⁽ⁱ⁾` of disjoint coordinates is that
product, the coordinates of each subsystem in place.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {ns n : ℕ} {d : Fin ns → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 15]: `Φ⁽¹⁾R⁽¹⁾ ⊕ ... ⊕ Φ⁽ⁿˢ⁾R⁽ⁿˢ⁾`, from the point `0`. -/
def NonlinDASys.composeSubsystems (Φ : ∀ i, Mat ℝ n (d i)) (R : ∀ i, Zonotope (Vec ℝ (d i))) :
    Zonotope (Vec ℝ n) :=
  (List.finRange ns).foldr (fun i Z => (Zonotope.mtimes (Φ i) (R i)).plus Z)
    (Zonotope.ofPoint 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
