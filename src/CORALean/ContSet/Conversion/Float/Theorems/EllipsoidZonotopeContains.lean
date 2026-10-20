module

public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeBoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsOuterFactorSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalCenterEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalDominated
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructSubsetOfLe
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# An ellipsoid lies in its zonotope, over a floating-point scalar

A certified factor `F` has `F Fᵀ ⪰ Q`, so the nominal ellipsoid lies in `{q + F u | ‖u‖₂ ≤ 1}`
(`construct_subset_of_le`), and `‖u‖₂ ≤ 1` bounds every coordinate of `u` by one: `u` is a
coefficient vector of the parallelotope. The error box is carried over. Without a certificate the
offset from the center lies in the box `q ± sqrt(diag(Q))` (`abs_sub_le_boxRadius`), which joins
the error box.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* ellipsoid is contained in its zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.zonotope_contains (E : Ellipsoid 𝕋 n) :
    E.construct ⊆ E.zonotope.construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, e, he, rfl⟩
  by_cases hok : Ellipsoid.isOuterFactor E.Q (Ellipsoid.outerFactor E.Q) = true
  · -- certified: `F Fᵀ ⪰ Q` dominates the nominal shape
    set F : Mat ℝ n n := toRealMat (Ellipsoid.outerFactor E.Q) with hF
    have hle : (F * Fᵀ - (nominal E).ellipsoid.Q).PosSemidef := by
      rcases Ellipsoid.nominal_dominated E with h | h
      · rw [h, sub_zero]
        simpa [conjTranspose_eq_transpose_of_trivial] using
          Matrix.posSemidef_self_mul_conjTranspose F
      · simpa [sub_add_sub_cancel] using (Ellipsoid.posSemidef_of_isOuterFactor hok).add h
    have hx' := Real.Ellipsoid.construct_subset_of_le (E₂ := Real.Ellipsoid.ofFactor F
      (toRealVec E.q)) hle (Ellipsoid.nominal_q E) hx
    rw [Real.Ellipsoid.construct_ofFactor] at hx'
    obtain ⟨u, hu, rfl⟩ := hx'
    -- `u` is a coefficient vector of the parallelotope on `F`'s columns
    unfold Ellipsoid.zonotope
    simp only [hok, if_true]
    refine ⟨toRealVec E.q + F *ᵥ u, ⟨u, fun j => le_trans (abs_le_norm₂ u j) hu, ?_⟩, e, he, rfl⟩
    congr 1
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, hF, toRealMat]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · -- uncertified: the center, and the offset in the box beside the error box
    have hbox : x - toRealVec E.q
        ∈ (Interval.symmetric (Ellipsoid.boxRadius 64 E)).construct := by
      rw [Interval.mem_vec_iff]
      intro i
      have h := Ellipsoid.abs_sub_le_boxRadius hx 64 i
      simp only [Interval.symmetric, Pi.neg_apply, toReal_neg', Pi.sub_apply, toRealVec]
      exact abs_le.mp h
    have hz : E.zonotope = ⟨0, E.q, Fin.elim0,
        E.I_error.plus (Interval.symmetric (Ellipsoid.boxRadius 64 E))⟩ := by
      show (if Ellipsoid.isOuterFactor E.Q (Ellipsoid.outerFactor E.Q) then _ else _) = _
      rw [if_neg hok]
    rw [hz]
    refine ⟨toRealVec E.q, ⟨Fin.elim0, fun j => j.elim0, ?_⟩, e + (x - toRealVec E.q),
      Interval.plus_outer _ _ ⟨e, he, _, hbox, rfl⟩, ?_⟩
    · show toRealVec E.q = toRealVec E.q + ∑ j : Fin 0, _
      rw [Fin.sum_univ_zero, add_zero]
    · show toRealVec E.q + (e + (x - toRealVec E.q)) = x + e
      rw [add_comm e, ← add_assoc, add_sub_cancel]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
