module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidConPolyZonoOfFactorConstruct
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Theorems.RelaxZero
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeBoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsOuterFactorSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalCenterEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalDominated
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructSubsetOfLe
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_ConPolyZono

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope, over a floating-point scalar

The nominal part of the conversion is the exact layer's conversion of the stored factor `G`
(`conPolyZonoOfFactor`), the set `{q + G u | ‖u‖₂ ≤ 1}`. A certified factor has `G Gᵀ ⪰ Q`, so
that set contains the nominal ellipsoid (`construct_subset_of_le`) and the error box is carried
over; an uncertified one is zero, and the nominal ellipsoid's offset from its center lies in the
box `q ± sqrt(diag(Q))` added to the error box (`abs_sub_le_boxRadius`). Outer either way.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* ellipsoid is contained in its constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored fields read as the exact layer's conversion of the chosen factor. -/
private theorem Ellipsoid.aux_nominal_conPolyZono (E : Ellipsoid 𝕋 n) : -- --- CONCL ---
    E.conPolyZono.nominalCore = Real.Ellipsoid.conPolyZonoOfFactor
      (toRealMat (if Ellipsoid.isOuterFactor E.Q (Ellipsoid.outerFactor E.Q) then
        Ellipsoid.outerFactor E.Q else fun _ _ => zero)) (toRealVec E.q) := by -- --- PROOF ---
  have hhalf : toReal (half (one : 𝕋)) = 1 / 2 := by rw [toReal_half, toReal_one]
  -- the fields agree entrywise
  show Real.ConPolyZono.mk _ _ _ _ _ _ _ (Real.PolyLevelSet.mk _ _ _ _ _ _ _) _ _ = _
  simp only [Real.Ellipsoid.conPolyZonoOfFactor]
  congr 1
  case e_GI => funext l i; exact l.elim0
  case e_cons =>
    congr 1
    case e_A =>
      funext i j
      change toReal (if j.val < n then (one : 𝕋) else neg (half one))
        = if j.val < n then (1 : ℝ) else -(1 / 2)
      split_ifs
      · exact toReal_one
      · rw [toReal_neg, hhalf]
    case e_b => funext i; exact hhalf
    case e_dom => exact Interval.nominal_unit _

/-- The factor form's set, read as the nominal part of the conversion. -/
private theorem Ellipsoid.aux_mem_nominalSet_conPolyZono (E : Ellipsoid 𝕋 n) {x : Vec ℝ n}
    (hx : ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧ x = toRealVec E.q + toRealMat
      (if Ellipsoid.isOuterFactor E.Q (Ellipsoid.outerFactor E.Q) then
        Ellipsoid.outerFactor E.Q else fun _ _ => zero) *ᵥ u) : -- --- CONCL ---
    x ∈ nominalSet E.conPolyZono := by -- --- PROOF ---
  -- the rows record no slack, so the nominal set is the stored fields' own
  have hs : toRealVec E.conPolyZono.cons.b_error = 0 := funext fun _ => toReal_zero
  show x ∈ (E.conPolyZono.nominalCore.relax (toRealVec E.conPolyZono.cons.b_error)).construct
  rw [hs, Real.ConPolyZono.relax_zero_construct, Ellipsoid.aux_nominal_conPolyZono,
    ← Real.Ellipsoid.conPolyZonoOfFactor_construct]
  exact hx


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.conPolyZono_contains (E : Ellipsoid 𝕋 n) : -- --- CONCL ---
    E.construct ⊆ E.conPolyZono.construct := by -- --- PROOF ---
  by_cases hok : Ellipsoid.isOuterFactor E.Q (Ellipsoid.outerFactor E.Q) = true
  · -- certified: `G Gᵀ ⪰ Q` dominates the nominal shape, and the error box is carried over
    refine mono_subset (fun x hx => ?_) (by
      change E.I_error.construct ⊆ (if Ellipsoid.isOuterFactor E.Q (Ellipsoid.outerFactor E.Q)
        then E.I_error else _ : Interval (Vec 𝕋 n)).construct
      rw [if_pos hok])
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
    refine Ellipsoid.aux_mem_nominalSet_conPolyZono E ?_
    rw [if_pos hok]
    exact hx'
  · -- uncertified: the center, and the offset in the box beside the error box
    rintro _ ⟨x, hx, e, he, rfl⟩
    have hbox : x - toRealVec E.q
        ∈ (Interval.symmetric (Ellipsoid.boxRadius 64 E)).construct := by
      rw [Interval.mem_vec_iff]
      intro i
      have h := Ellipsoid.abs_sub_le_boxRadius hx 64 i
      simp only [Interval.symmetric, Pi.neg_apply, toReal_neg', Pi.sub_apply, toRealVec]
      exact abs_le.mp h
    have hc : toRealVec E.q ∈ nominalSet E.conPolyZono :=
      Ellipsoid.aux_mem_nominalSet_conPolyZono E ⟨0, by rw [norm₂_zero]; exact zero_le_one,
        by rw [Matrix.mulVec_zero, add_zero]⟩
    refine ⟨toRealVec E.q, hc, e + (x - toRealVec E.q), ?_, by abel⟩
    change _ ∈ (if Ellipsoid.isOuterFactor E.Q (Ellipsoid.outerFactor E.Q)
      then E.I_error else _ : Interval (Vec 𝕋 n)).construct
    rw [if_neg hok]
    exact Interval.plus_outer _ _ ⟨e, he, _, hbox, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
