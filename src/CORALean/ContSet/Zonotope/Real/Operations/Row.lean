import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.row`

The `i`-th dimension of a zonotope as a zonotope of its own, `H(i) = ⟨c(i), G(i, ·)⟩ ⊂ ℝ`: the
`i`-th entry of the centre and of every generator, the generator count unchanged. [1, Prop. 12]
differentiates the slope and the approximation errors of an image enclosure with respect to it,
`∇_{H_{k-1}(i)} m_k(i)`, these depending on the input set through the `i`-th row alone.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.row (H : Zonotope (Vec ℝ n)) (i : Fin n) : Zonotope (Vec ℝ 1) where
  h := H.h
  c := fun _ => H.c i
  G := fun j _ => H.G j i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
