module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Operations.IntersectStripCora
public import CORALean.ContSet.Zonotope.Float.Theorems.IntersectStripOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ToSetPoint

@[expose] public section

/-!
# `Zonotope.intersectStripCora` encloses the intersection with the strips

A point `x` of `Z` in the strips is `c + x₀`, `x₀` in the centered zonotope and in the strips
`|C x₀ - y₀| ≤ φ'` at the shifted measurement `y₀` and the widened `φ'` (the residual `y - C c`
lies in the interval whose lower end is `y₀` and whose width is in `φ'`). Then
`Zonotope.intersectStrip_outer` puts `x₀` in the inner zonotope, and `Zonotope.plus_outer` adds `c`.

## Inputs
* `C` – measurement matrix
* `φ` – strip half-widths
* `y` – measurement
* `Λ` – weight matrix
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* intersection with the strip is contained in the computed zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of `Z` less its center is a point of the centered zonotope. -/
private theorem Zonotope.aux_centered_mem (Z : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ Z.toSet) : -- --- CONCL ---
    x - toRealVec Z.c ∈
      ({ Z with c := fun _ => zero } : Zonotope (Vec 𝕋 n)).toSet := by -- --- PROOF ---
  obtain ⟨z, hz, e, he, rfl⟩ := hx
  obtain ⟨β, hβ, hzβ⟩ := Zonotope.mem_nominalSet_iff.mp hz
  refine ⟨z - toRealVec Z.c, ?_, e, he, ?_⟩
  swap
  · funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  refine Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => ?_⟩
  simp only [Pi.sub_apply, toRealVec, toReal_zero, zero_add]
  rw [hzβ i]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intersection with the strip lies in the zonotope with CORA.cpp's center. -/
theorem Zonotope.intersectStripCora_outer (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : Mat 𝕋 n p)
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Z.toSet ∩ {x | ∀ i, |(toRealMat C *ᵥ x - toRealVec y) i| ≤ toReal (φ i)} ⊆
      (Z.intersectStripCora C φ y Λ).toSet := by -- --- PROOF ---
  rintro x ⟨hx, hs⟩
  -- the names of the definition: `C c` rounded, the new measurement and the widened half-widths
  set Cc := Zonotope.step_stripCenterImage C Z.c with hCcdef
  set y₀ := Zonotope.step_stripShiftedY C y Z.c with hy₀
  set φ' := Zonotope.step_stripShiftedPhi C φ y Z.c with hφ'
  -- `C c` lies in its rounded column
  have hCc : toRealMat C * toRealMat (fun j (_ : Fin 1) => Z.c j : Mat 𝕋 n 1) ∈ Cc.toSet :=
    Interval.matMul_outer (Interval.point C) (Interval.point fun j (_ : Fin 1) => Z.c j)
      (Interval.mem_point C) (Interval.mem_point _)
  have hCcEntry : ∀ i, toReal (Cc.inf i 0) ≤ (toRealMat C *ᵥ toRealVec Z.c) i ∧
      (toRealMat C *ᵥ toRealVec Z.c) i ≤ toReal (Cc.sup i 0) := by
    intro i
    have := Interval.mem_mat_iff.mp hCc i 0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, toRealVec, toRealMat] using this
  -- the shifted strips: `|C (x - c) - y₀| ≤ φ'`
  have hs' : ∀ i, |(toRealMat C *ᵥ (x - toRealVec Z.c) - toRealVec y₀) i| ≤ toReal (φ' i) := by
    intro i
    obtain ⟨hlo, hhi⟩ := hCcEntry i
    have h1 := abs_le.mp (hs i)
    -- the residual `y - C c` lies between `y₀` and the upper end, whose width is in `φ'`
    have hd1 : toReal (y₀ i) ≤ toReal (y i) - toReal (Cc.sup i 0) :=
      subDown_le_sub (y i) (Cc.sup i 0)
    have hd2 := sub_le_subUp (y i) (Cc.inf i 0)
    have hw := sub_le_subUp (subUp (y i) (Cc.inf i 0)) (y₀ i)
    have hph := add_le_addUp (φ i) (subUp (subUp (y i) (Cc.inf i 0)) (y₀ i))
    have hsub : (toRealMat C *ᵥ (x - toRealVec Z.c)) i =
        (toRealMat C *ᵥ x) i - (toRealMat C *ᵥ toRealVec Z.c) i := by
      rw [Matrix.mulVec_sub]; rfl
    have hphi : toReal (φ' i) = toReal (addUp (φ i) (subUp (subUp (y i) (Cc.inf i 0)) (y₀ i))) :=
      rfl
    have hlhs : (toRealMat C *ᵥ (x - toRealVec Z.c) - toRealVec y₀) i
        = (toRealMat C *ᵥ x) i - (toRealMat C *ᵥ toRealVec Z.c) i - toReal (y₀ i) := by
      rw [Pi.sub_apply, hsub]; rfl
    have hy : (toRealMat C *ᵥ x - toRealVec y) i = (toRealMat C *ᵥ x) i - toReal (y i) := rfl
    rw [hy] at h1
    rw [hlhs, hphi]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [h1.1, h1.2]
  -- the centered zonotope with the shifted strips, then `c` added back
  have h0 := Zonotope.intersectStrip_outer C φ' y₀ Λ { Z with c := fun _ => zero }
    ⟨Zonotope.aux_centered_mem Z hx, hs'⟩
  refine Zonotope.plus_outer _ _ ⟨toRealVec Z.c, ?_, x - toRealVec Z.c, h0, ?_⟩
  · rw [Zonotope.toSet_point]
    exact Set.mem_singleton _
  · funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
