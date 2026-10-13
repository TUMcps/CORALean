import CORALean.ContSet.Interval.Float.Theorems.OriginExact
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffStretch
import CORALean.ContSet.Zonotope.Float.Theorems.OfEntryBoundsOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffStretchOuter

/-!
# The float `minkDiffStretch` over-approximates the Minkowski difference

[1, Thm. 5], CORA's `'outer'` and `'outer:coarse'`, at a float result. Two steps: the float
stretch, every entry bracketed and the gaps paid into the box, encloses the real stretch of the
operands' nominal zonotopes at `μ` read as reals (`aux_minkDiffStretch_encloses`, by
`ofEntryBounds_outer`); and at a `μ` meeting [1, Thm. 5]'s constraint that real stretch covers
the difference (`Real.Zonotope.minkDiffStretch_outer`, whose hypotheses this theorem asks for
verbatim at the nominal operands).

The difference is the one of the nominal zonotopes. A box on the subtrahend only shrinks the true
difference, so it is still covered; a box on the minuend can grow it beyond what the stretched
nominal minuend reaches, and [1, Thm. 5] says nothing about that set.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The float stretch encloses the real one at the nominal operands and `μ` read as reals. -/
theorem Zonotope.aux_minkDiffStretch_encloses (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (μ : Fin Z₁.h → 𝕋) :
    (Z₁.nominal.minkDiffStretch Z₂.nominal fun υ => toReal (μ υ)).construct
      ⊆ (Z₁.minkDiffStretch Z₂ μ).construct := by -- --- PROOF ---
  intro x hx
  have h := Zonotope.ofEntryBounds_outer (Z₁.nominal.minkDiffStretch Z₂.nominal
      fun υ => toReal (μ υ)) (Interval.origin n)
    (cLo := fun r => subDown (Z₁.c r) (Z₂.c r)) (cHi := fun r => subUp (Z₁.c r) (Z₂.c r))
    (GLo := fun r i => mulDown (μ i) (Z₁.G i r)) (GHi := fun r i => mulUp (μ i) (Z₁.G i r))
    (fun r => ⟨subDown_le_sub _ _, sub_le_subUp _ _⟩)
    (fun r i => ⟨mulDown_le_mul _ _, mul_le_mulUp _ _⟩)
  rw [Interval.origin_exact, Set.add_singleton] at h
  exact h ⟨x, hx, add_zero x⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 5] at a float result: at a `μ` meeting its constraint, read as reals, the float
stretch covers the Minkowski difference of the nominal operands. -/
theorem Zonotope.minkDiffStretch_outer {ι : Type} (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (μ : Fin Z₁.h → 𝕋)
    (C : ι → (Vec ℝ n →ₗ[ℝ] ℝ)) (hμ0 : ∀ υ, 0 ≤ toReal (μ υ)) (b : ι → ℝ)
    (hb : ∀ i, ∀ x ∈ minkowskiDiff Z₁.nominal.construct Z₂.nominal.construct,
      C i (x - (Z₁.nominal.c - Z₂.nominal.c)) ≤ b i)
    (hμ : ∀ i, b i ≤ ∑ υ, |C i (Z₁.nominal.G υ)| * toReal (μ υ))
    (hCd : {y | ∀ i, C i (y - (Z₁.nominal.minkDiffStretch Z₂.nominal fun υ => toReal (μ υ)).c)
                ≤ ∑ υ, |C i ((Z₁.nominal.minkDiffStretch Z₂.nominal fun υ => toReal (μ υ)).G υ)|}
            ⊆ (Z₁.nominal.minkDiffStretch Z₂.nominal fun υ => toReal (μ υ)).construct) :
    minkowskiDiff Z₁.nominal.construct Z₂.nominal.construct
      ⊆ (Z₁.minkDiffStretch Z₂ μ).construct :=
  subset_trans (Z₁.nominal.minkDiffStretch_outer Z₂.nominal C _ hμ0 b hb hμ hCd)
    (Zonotope.aux_minkDiffStretch_encloses Z₁ Z₂ μ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
