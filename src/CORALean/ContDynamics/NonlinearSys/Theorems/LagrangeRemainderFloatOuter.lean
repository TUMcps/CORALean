module

public import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainderFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LagrangeRemainderMono
public import CORALean.ContDynamics.NonlinearSys.Theorems.ZonotopeRadiusAttained
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The float cubic remainder holds the exact one

Where a float zonotope holds the exact one and a float `E` bounds the exact `E` entrywise in
magnitude, `lagrangeRemainderFloat`'s box holds `lagrangeRemainder`'s. The radius `γ` of the exact
zonotope is attained at a point of it (`aux_radius_attained`), which lies in the float zonotope's
box, so the float `γ` bounds it; `abs_bilin_le_bilinUp` bounds the form and the sixth is `11/64 ≥
1/6`. See [1].

## Inputs
* `d` – dimension
* `n` – output dimension
* `Ef` – float third-derivative bounds
* `E` – exact third-derivative bounds
* `Z` – float zonotope
* `Zr` – exact zonotope
* `zs` – expansion point

## Hypotheses
* `hE` – float bounds dominate exact ones
* `hZ` – float zonotope holds exact one

## Conclusion
* the exact remainder box is inside the float one

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact third-order remainder box over a zonotope held by `Z` is inside the float one. -/
theorem lagrangeRemainderFloat_outer {d n : ℕ} {Ef : Fin n → Fin d → Mat 𝕋 d d}
    {E : Fin n → Fin d → Mat ℝ d d} (hE : ∀ i j k l, |E i j k l| ≤ toReal (Ef i j k l))
    {Z : Zonotope (Vec 𝕋 d)} {Zr : Real.Zonotope (Vec ℝ d)} (hZ : Zr.construct ⊆ Z.construct)
    (zs : Vec 𝕋 d) : -- --- CONCL ---
    (lagrangeRemainder E Zr (toRealVec zs)).construct ⊆
      (lagrangeRemainderFloat Ef Z zs).construct := by -- --- PROOF ---
  intro y hy i
  set γ : Vec 𝕋 d := (Interval.plus Z.interval (Interval.point (-zs))).normMag
    with hγ
  set γr : Vec ℝ d := fun j => |Zr.c j - toRealVec zs j| + ∑ k, |Zr.G k j| with hγr
  -- the exact radius is attained inside the float zonotope's box, so the float one bounds it
  have hle : ∀ j, γr j ≤ toReal (γ j) := fun j => by
    obtain ⟨z, hz, hat⟩ := Real.Zonotope.radius_attained Zr (toRealVec zs) j
    refine le_trans hat ?_
    -- `z - z✱` is in the box `Z' - z✱`, whose largest magnitude is `normMag`
    have hbox := Interval.plus_outer Z.interval (Interval.point (-zs))
      (Set.add_mem_add (Zonotope.interval_contains Z (hZ hz))
        (Interval.mem_point (α := Vec 𝕋 d) (-zs)))
    have hneg : (RealImage.realImage (α := Vec 𝕋 d) (-zs) : Vec ℝ d) =
        -toRealVec zs := funext fun j => toReal_neg (zs j)
    rw [hneg, ← sub_eq_add_neg] at hbox
    obtain ⟨h1, h2⟩ := hbox j
    simp only [hγ, Interval.normMag, toReal_maximum, toReal_absolute]
    exact abs_le_max_abs_abs h1 h2
  have h0 : ∀ j, 0 ≤ γr j := fun j =>
    add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  -- each summand of the box's half-width
  have hq : ∀ j, |γr ⬝ᵥ (E i j *ᵥ γr)| ≤
      toReal (bilinUp γ (fun k l => absolute (Ef i j k l)) γ) := fun j =>
    abs_bilin_le_bilinUp (fun k => by rw [abs_of_nonneg (h0 k)]; exact hle k)
      (fun k => by rw [abs_of_nonneg (h0 k)]; exact hle k)
      (fun k l => by
        rw [toReal_absolute]
        exact le_trans (hE i j k l) (le_abs_self _))
  have hsum : |∑ j, γr j * (γr ⬝ᵥ (E i j *ᵥ γr))| ≤
      toReal (sumUp fun j => mulUp (γ j) (bilinUp γ (fun k l => absolute (Ef i j k l)) γ)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_of_nonneg (h0 j)]
    exact le_trans (mul_le_mul (hle j) (hq j) (abs_nonneg _) (le_trans (h0 j) (hle j)))
      (mul_le_mulUp _ _)
  -- the sixth, `11/64 ≥ 1/6`
  have hsix : (1 : ℝ) / 6 ≤ toReal (addUp (half (half (half (one : 𝕋))))
      (addUp (half (half (half (half (half (one : 𝕋)))))) (half (half (half (half (half (half
        (one : 𝕋))))))))) := by
    refine le_trans ?_ (add_le_addUp _ _)
    refine le_trans ?_ (add_le_add le_rfl (add_le_addUp _ _))
    simp only [toReal_half, toReal_one]
    norm_num
  -- `hy` says the exact half-width is non-negative, and bounds the point
  obtain ⟨h1, h2⟩ := hy i
  simp only [lagrangeRemainder] at h1 h2
  have h1' : -((∑ j, γr j * (γr ⬝ᵥ (E i j *ᵥ γr))) / 6) ≤ y i := h1
  have h2' : y i ≤ (∑ j, γr j * (γr ⬝ᵥ (E i j *ᵥ γr))) / 6 := h2
  set T := toReal (sumUp fun j => mulUp (γ j) (bilinUp γ (fun k l => absolute (Ef i j k l)) γ))
    with hT
  have hT0 : 0 ≤ T := le_trans (abs_nonneg _) hsum
  have hL : (∑ j, γr j * (γr ⬝ᵥ (E i j *ᵥ γr))) / 6 ≤ toReal (mulUp
      (sumUp fun j => mulUp (γ j) (bilinUp γ (fun k l => absolute (Ef i j k l)) γ))
      (addUp (half (half (half (one : 𝕋)))) (addUp (half (half (half (half (half
        (one : 𝕋)))))) (half (half (half (half (half (half (one : 𝕋)))))))))) := by
    refine le_trans ?_ (mul_le_mulUp _ _)
    calc (∑ j, γr j * (γr ⬝ᵥ (E i j *ᵥ γr))) / 6 ≤ T / 6 := by
          linarith [le_abs_self (∑ j, γr j * (γr ⬝ᵥ (E i j *ᵥ γr)))]
      _ = T * (1 / 6) := by ring
      _ ≤ T * _ := mul_le_mul_of_nonneg_left hsix hT0
  show toReal (neg _) ≤ y i ∧ y i ≤ toReal _
  rw [toReal_neg]
  exact ⟨by linarith, le_trans h2' hL⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
