module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.unitIntervalMul`

[1, Eq. 11]: the scalar interval multiplication `[-1, 1] ⊗ Z`, enclosed by the zonotope
`(0, c, g⁽¹⁾, ..., g⁽ᵖ⁾)` — the centre made a generator of its own and the new centre the
origin. Not exact: `s(c + Σ βⱼg⁽ʲ⁾)` ties the centre's coefficient `s` to the others',
`sβⱼ`, and the zonotope frees them, which `unitIntervalMul_outer` spends.

Over any real module, like `Zonotope` itself: [1, Thm. 1] applies it to vectors.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 11]: the zonotope `(0, c, g⁽¹⁾, ..., g⁽ᵖ⁾)` enclosing `[-1, 1] ⊗ Z`. -/
def Zonotope.unitIntervalMul (Z : Zonotope α) : Zonotope α where
  h := Z.h + 1
  c := 0
  G := Fin.cons Z.c Z.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
