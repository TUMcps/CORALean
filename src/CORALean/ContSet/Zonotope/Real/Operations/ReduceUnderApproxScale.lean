import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.reduceUnderApproxScale`

The scaling method of [1, Sec. IV-C], Step 2): scale each generator `g_{o,i}` of a template
`Z_o = ⟨c, G_o⟩` by `λ(i)`. The template (Step 1, an overapproximative order reduction) and the
factors `λ` (the linear program, maximizing `Σ λ(i) ‖g_{o,i}‖₂`) are arguments; the factor is `lam`
as `λ` is Lean's.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. IV-C]: `Ẑ = ⟨c, G_o diag(λ)⟩`, with the centre of `Z`. -/
def Zonotope.reduceUnderApproxScale (Z Zo : Zonotope α) (lam : Fin Zo.h → ℝ) : Zonotope α :=
  ⟨Zo.h, Z.c, fun i => lam i • Zo.G i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
