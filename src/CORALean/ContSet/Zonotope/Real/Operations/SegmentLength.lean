import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.segmentLength`

[1, Eq. 46]: the size `Sm(Z(R)) = Σᵢ Σⱼ Rᵢⱼ² = ‖R‖²_F = Tr(RᵀR)` of a zonotope by the sum of
squares of its generators' entries, the criterion CORA's `aux_enclosePointsMaiga` minimises over
`ratio` (`trace(G' * G)`, "estimate the volume of the zonotope using the trace").

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Sm(Z(R)) = ‖R‖²_F`. -/
def Zonotope.segmentLength (Z : Zonotope (Vec ℝ n)) : ℝ := ∑ j, ∑ i, Z.G j i ^ 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
