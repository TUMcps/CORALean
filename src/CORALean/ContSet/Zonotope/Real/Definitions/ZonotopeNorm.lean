module

public import CORALean.ContSet.Zonotope.Real.Operations.GenMap
public import CORALean.Global.CoeffNorm
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# The zonotope norm

`[1, Def. 4]`: `‖p‖_Z = ν(p) = min {‖γ‖∞ | G γ = p}` (the paper's Eq. 6), the generator map's
`coeffNorm` at the supremum norm of the coefficients. CORA's `zonotopeNorm(Z, p)` also ignores the
center: a point is measured from `c` as `‖p - c‖_Z`. It is a norm for a non-degenerate `Z`
(`zonotopeNorm_isNorm`). Off the range of the generators the paper leaves it undefined and CORA
returns `Inf`, the minimum over the empty set. `zonotopeNorm` is real-valued and reads `0` there,
a convention no theorem uses (each assumes a surjective generator map or a preimage);
`zonotopeNormE` is an `EReal`, `⊤` there, and `zonotopeNorm` wherever a preimage exists.

## Inputs
* `Z` – zonotope
* `p` – point

## Output
* zonotope norm of `p`

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../../../../references/2021/kulmburg-ejc-zonotope-containment.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   03-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `‖p‖_Z`, `[1, Def. 4]`, `0` for a point no generator coefficients reach (a convention: use
`Zonotope.zonotopeNormE` for the value there). -/
noncomputable def Zonotope.zonotopeNorm (Z : Zonotope α) (p : α) : ℝ := coeffNorm Z.genMap p

/-- `min {‖γ‖∞ | G γ = p}` as CORA's `zonotopeNorm` returns it, the infimum over every coefficient
vector reaching `p`: `⊤` (`Inf`) where none does. -/
noncomputable def Zonotope.zonotopeNormE (Z : Zonotope α) (p : α) : EReal :=
  sInf ((fun γ : Vec ℝ Z.h => ((‖γ‖ : ℝ) : EReal)) '' {γ | Z.genMap γ = p})

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
