module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionPointMem
public import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionExact
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter

@[expose] public section

/-!
# `ConPolyZono.union` contains both operands

The exact layer's union is exact on the read-back operands (`union_exact_of_noZeroCol`), and a
point of an operand is such a point moved by a vector of its box, which lies in the hull of both
boxes (`Interval.or_outer`). `union_point_mem` places that sum in the stored union.

The hypotheses are the exact layer's: no independent generators, a bound `b` that does not cross,
and no all-zero exponent column in any of the four exponent matrices. Without the last, [1, Thm. 1]
fails even over ℝ. Outer, never exact: the stored union also contains what rounding admits.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.union_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (hq₁ : cPZ₁.qI = 0) (hq₂ : cPZ₂.qI = 0)
    (hb₁ : cPZ₁.b.nominal.IsNonempty (ι := Fin cPZ₁.m))
    (hb₂ : cPZ₂.b.nominal.IsNonempty (ι := Fin cPZ₂.m))
    (hE₁ : Real.ConPolyZono.NoZeroCol cPZ₁.E) (hR₁ : Real.ConPolyZono.NoZeroCol cPZ₁.R)
    (hE₂ : Real.ConPolyZono.NoZeroCol cPZ₂.E)
    (hR₂ : Real.ConPolyZono.NoZeroCol cPZ₂.R) : -- --- STMT ---
    cPZ₁.construct ∪ cPZ₂.construct ⊆ (cPZ₁.union cPZ₂).construct := by -- --- PROOF ---
  -- the exact union of the read-back operands holds both nominal sets
  have hex := Real.ConPolyZono.union_exact_of_noZeroCol (nominal cPZ₁) (nominal cPZ₂)
    hq₁ hq₂ hb₁ hb₂ hE₁ hR₁ hE₂ hR₂
  rintro x (⟨y, hy, e, he, rfl⟩ | ⟨y, hy, e, he, rfl⟩)
  · exact ConPolyZono.union_point_mem cPZ₁ cPZ₂ (hex ▸ Or.inl hy)
      (Interval.or_outer _ _ (Or.inl he))
  · exact ConPolyZono.union_point_mem cPZ₁ cPZ₂ (hex ▸ Or.inr hy)
      (Interval.or_outer _ _ (Or.inr he))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
