import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Goffin's separator for a zonotope

[1, Sec. 4.5]: for `x₀ = γe_{i₀} ∉ Z`, Step 1 takes `β* := max{β | βx₀ ∈ Z}` (a linear program)
and `x* := β*x₀ ∈ ∂Z`; Steps 2 and 3 find a facet `F(x*)` through `x*` and its basis
`{h₁, …, h_{n-1}} = bas(F(x*))` (Cor. 3.5, Thm. 3.3(d)); Step 4 outputs
`a := (I - H(HᵀH)⁻¹Hᵀ)x₀`, `H = (h₁, …, h_{n-1})`. The steps that search (the linear program and
the facet) are the caller's: `β*` and `H` are arguments, and `GoffinSeparatorSpec` states what
they must satisfy. The offset `b = aᵀx*` is the one [1] leaves implicit, the value of `aᵀx` on
the facet's affine hull.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 4.5]: the separator `aᵀx ≤ b` of `x₀`, from `β*` (Step 1) and `H = bas(F(x*))`
(Steps 2 and 3). -/
noncomputable def Zonotope.goffinSeparator (βstar : ℝ) (x₀ : Vec ℝ n) (H : Mat ℝ n k) :
    Vec ℝ n × ℝ :=
  let xstar := βstar • x₀
  let a := (1 - H * (Hᵀ * H)⁻¹ * Hᵀ) *ᵥ x₀
  (a, a ⬝ᵥ xstar)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
