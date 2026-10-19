module

public import CORALean.Specification.SyntaxTree.Operations.Nthroot

@[expose] public section

/-!
# `nthroot` for an integer degree

`nthroot(x,e)` of MATLAB for `e < 0` is `1 / nthroot(x,-e)`. The real layer has no infinite bound,
so `nthroot(0,e) = Inf` for `e < 0` is not modelled: the value there is `0`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (interval
arithmetic over `𝕋` with outward rounding) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `nthroot(x,e)` for an integer degree: `1 / nthroot(x,-e)` for `e < 0`. -/
noncomputable def SyntaxTree.nthrootZ (x : ℝ) (e : ℤ) : ℝ :=
  if 0 ≤ e then nthroot x e.toNat else (nthroot x (-e).toNat)⁻¹

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
