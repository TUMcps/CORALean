module

public import CORALean.ContSet.Conversion.Real.Operations.Capsule_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidZonotopeContains
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# A capsule as a zonotope

CORA's conversion: the segment, exactly, plus the zonotope of the ball (`Ellipsoid.zonotope` of
`ellipsoid(r² I)`), or the segment alone at `r = 0`. A point of the capsule is a point `c + t g` of
the segment plus a vector of length at most `r`, which `r · (y / r)` writes as the image of the
unit ball under `r I`, the ellipsoid's own set (`Ellipsoid.construct_ofFactor`).

## Inputs
* `C` – capsule

## Hypotheses
* none

## Conclusion
* capsule is contained in its zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.zonotope_contains (C : Capsule n) :
    C.construct ⊆ C.zonotope.construct := by -- --- PROOF ---
  rintro x ⟨t, ht, hle⟩
  -- what the segment point `c + t g` leaves of `x`
  set y : Vec ℝ n := x - (C.c + t • C.g) with hy
  have hy2 : ‖y‖₂ ≤ C.r := by
    have h : ‖y‖₂ = Real.sqrt (∑ i, (x i - (C.c i + t * C.g i)) ^ 2) := by
      simp [CORALean.norm₂, hy]
    rwa [h]
  have hseg : C.c + t • C.g ∈ (⟨1, C.c, fun _ => C.g⟩ : Zonotope (Vec ℝ n)).construct :=
    ⟨fun _ => t, fun _ => abs_le.mpr ht, by simp⟩
  unfold Capsule.zonotope
  split_ifs with hr
  · -- `r = 0`: the segment alone, and `y = 0`
    have hy0 : y = 0 := by
      have h0 : ‖y‖₂ = 0 := le_antisymm (hr ▸ hy2) (norm₂_nonneg y)
      funext i
      have h1 : ∑ i, y i ^ 2 = 0 := by
        have := congrArg (· ^ 2) h0
        simpa [CORALean.norm₂, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (y i))]
          using this
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (y i)).mp h1 i
        (Finset.mem_univ i)
      simpa using h2
    have hx : x = C.c + t • C.g := sub_eq_zero.mp hy0
    rwa [hx]
  · -- the ball's part, `r · (y / r)`
    have hr0 : 0 < C.r := lt_of_le_of_ne (le_trans (norm₂_nonneg y) hy2) (Ne.symm hr)
    rw [← Zonotope.plus_exact]
    refine ⟨C.c + t • C.g, hseg, (C.r • (1 : Mat ℝ n n)) *ᵥ (C.r⁻¹ • y), ?_, ?_⟩
    · apply Ellipsoid.zonotope_contains
      rw [Ellipsoid.construct_ofFactor]
      refine ⟨C.r⁻¹ • y, ?_, by simp⟩
      rw [norm₂_smul, abs_of_pos (inv_pos.mpr hr0)]
      calc C.r⁻¹ * ‖y‖₂ ≤ C.r⁻¹ * C.r := mul_le_mul_of_nonneg_left hy2 (inv_nonneg.mpr hr0.le)
        _ = 1 := inv_mul_cancel₀ hr
    · rw [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hr, one_smul, hy]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
