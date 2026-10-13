import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRowNormal

/-!
# The offset of one signed row of [1, Thm. 3]

`d = C (c⁽ᵐ⁾ − c⁽ˢ⁾) + Δd − Δd_trans` at the row `(b, T)` of `Zonotope.minkDiffRowNormal`: the
normal paired with the centre difference, plus the minuend's reach in that direction less the
subtrahend's.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The offset of the signed row `(b, T)` of `Z_m ⊖ Z_s`: the normal at the centre difference plus
`Δd − Δd_trans`. -/
noncomputable def Zonotope.minkDiffRowOffset {n : ℕ} (Zm Zs : Zonotope (Vec ℝ (n + 2)))
    (j : Bool × Finset (Fin Zm.h)) : ℝ :=
  Zm.minkDiffRowNormal j ⬝ᵥ (Zm.c - Zs.c) +
    ((∑ υ, |Zm.minkDiffRowNormal j ⬝ᵥ Zm.G υ|) - ∑ υ, |Zm.minkDiffRowNormal j ⬝ᵥ Zs.G υ|)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
