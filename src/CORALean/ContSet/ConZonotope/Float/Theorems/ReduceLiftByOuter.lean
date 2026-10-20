module

public import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLiftBy
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemKeepColsNominal
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByCoeff

@[expose] public section

/-!
# Lifting, reducing and reading the rows back over-approximates, in floats

[1, Sec. 4.3] on the stored floats.

A point `y + e` of `cZ`, `y` nominal at `β`: `Zonotope.reduceBy_coeff` on the lifted zonotope
gives coefficients `ξ` that agree with `β` on the kept generators and reproduce every
coordinate of the lifted sum. The upper coordinates are `y`, so the point is the result's
nominal point at `ξ` plus the same `e`. The lower coordinates are `Aₑ β`, which the new
equality rows read at `ξ` as the same number, within the carried slack of the unchanged `bₑ`. The
inequality rows at `ξ` are those at `β` on the kept generators (`HPolytope.mem_keepCols_nominal`).

## Inputs
* `cZ` – float constrained zonotope
* `part` – generator partition

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceLiftBy_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) :
    cZ.construct ⊆ (cZ.reduceLiftBy part).construct := by -- --- PROOF ---
  rintro x ⟨y, hy', e, he, hx⟩
  obtain ⟨β, hβ, hP, hy⟩ := ConZonotope.mem_nominalSet_iff.mp hy'
  obtain ⟨hPin, hPeq⟩ := HPolytope.mem_nominal_iff.mp hP
  obtain ⟨ξ, hξ, hξl, hsum⟩ := Zonotope.reduceBy_coeff cZ.liftEq part β hβ
  refine ⟨y, ConZonotope.mem_nominalSet_iff.mpr ⟨ξ, hξ, ?_, fun k => ?_⟩, e, he, hx⟩
  · refine HPolytope.mem_stackRows_nominal_iff.mpr ⟨?_, HPolytope.mem_nominal_iff.mpr
      ⟨fun i => i.elim0, fun i => ?_⟩⟩
    · -- the inequality rows: the kept coefficients, the fresh ones read as zero
      show ξ ∈ (((cZ.P.keepCols part).dropEqs).padLeft (n + cZ.P.me)).nominal.construct
      rw [HPolytope.mem_padLeft_nominal_iff]
      have hk := HPolytope.mem_keepCols_nominal cZ.P part hP fun l => hβ (part.right l)
      have hl : blockLeft q (n + cZ.P.me) ξ = fun l => β (part.left l) := funext hξl
      rw [hl]
      exact HPolytope.mem_nominal_iff.mpr ⟨(HPolytope.mem_nominal_iff.mp hk).1, fun i => i.elim0⟩
    · -- the lower coordinates of the lifted sum are the original equality rows
      have heq := hPeq i
      simp only [mulVec, dotProduct, toRealMat] at heq ⊢
      have hs := hsum (Fin.natAdd n i)
      simp only [ConZonotope.liftEq, Fin.append_right] at hs
      have key : ∑ j : Fin (cZ.liftEq.reduceBy part).h,
          toReal ((cZ.liftEq.reduceBy part).G j (Fin.natAdd n i)) * ξ j
          = ∑ j, toReal (cZ.P.Ae i j) * β j := hs.symm
      exact key ▸ heq
  · -- the upper coordinates are the point itself
    have hs := hsum (Fin.castAdd cZ.P.me k)
    simp only [ConZonotope.liftEq, Fin.append_left] at hs
    rw [hy k]
    exact congrArg (toReal (cZ.c k) + ·) hs

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
