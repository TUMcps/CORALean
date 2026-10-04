import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach

/-!
# A passed `ConZonotope.interiorCert` puts a box of points in the nominal set

A point `y` within `B` of `y₀ = c + G β₀` is `y₀ + G β'` for coefficients `β'` of size at most `δ`
(`Zonotope.ballCert_reach`). The coefficients `β₀ + β'` stay in the unit box and in every row of
the constraint polytope, since each row moves by at most `δ` times its absolute sum, which the
check has charged.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row applied to a short vector moves by at most its absolute sum times the bound. -/
theorem ConZonotope.aux_row_move {m h : ℕ} (M : Mat 𝕋 m h) (v : Vec ℝ h) {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : ∀ j, |v j| ≤ δ) (i : Fin m) :
    |(toRealMat M *ᵥ v) i| ≤ δ * toReal (radius M i) := by -- --- PROOF ---
  calc |(toRealMat M *ᵥ v) i| = |∑ j, toReal (M i j) * v j| := rfl
    _ ≤ ∑ j, |toReal (M i j) * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |toReal (M i j)| * δ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = δ * ∑ j, |toReal (M i j)| := by rw [← Finset.sum_mul]; ring
    _ ≤ δ * toReal (radius M i) := mul_le_mul_of_nonneg_left (sum_abs_le_radius i) hδ


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.box_subset {cZ : ConZonotope 𝕋 n} {H : Mat 𝕋 cZ.h n} {β₀ : Vec 𝕋 cZ.h}
    {δ B : 𝕋} (hc : cZ.interiorCert H β₀ δ B = true) (y : Vec ℝ n)
    (hy : ∀ i, |y i - (toReal (cZ.c i) + ∑ j, toReal (cZ.G i j) * toReal (β₀ j))| ≤ toReal B) :
    y ∈ nominalSet cZ := by -- --- PROOF ---
  simp only [ConZonotope.interiorCert, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at hc
  obtain ⟨⟨⟨⟨hδ0, hbox⟩, hineq⟩, heq⟩, hball⟩ := hc
  have hδ : 0 ≤ toReal δ := by simpa [toReal_zero] using toReal_le_of_le hδ0
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hball
  obtain ⟨β', hβ', hβδ⟩ := hreach (fun i => y i - (toReal (cZ.c i)
    + ∑ j, toReal (cZ.G i j) * toReal (β₀ j))) hy
  -- the coefficients `β₀ + β'`: in the unit box, in the constraint polytope, reaching `y`
  refine ConZonotope.mem_nominalSet_iff.mpr
    ⟨fun j => toReal (β₀ j) + β' j, fun j => ?_, ?_, fun i => ?_⟩
  · -- the unit box
    have h1 := toReal_le_of_le (hbox j)
    have h2 := add_le_addUp (absolute (β₀ j)) δ
    rw [toReal_absolute, toReal_one] at *
    calc |toReal (β₀ j) + β' j| ≤ |toReal (β₀ j)| + |β' j| := abs_add_le _ _
      _ ≤ 1 := by linarith [hβδ j]
  · -- the constraint rows
    rw [HPolytope.mem_construct_iff]
    have hsplit : ∀ {m : ℕ} (M : Mat 𝕋 m cZ.h) (i : Fin m),
        (toRealMat M *ᵥ fun j => toReal (β₀ j) + β' j) i
          = ∑ j, toReal (M i j) * toReal (β₀ j) + (toRealMat M *ᵥ β') i := by
      intro m M i
      simp only [Matrix.mulVec, dotProduct, toRealMat]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- the inequality rows, then the lower and the upper end of each slab row
    refine ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
    · have h1 := toReal_le_of_le (hineq i)
      have h2 := add_le_addUp (dotUp (cZ.P.A i) β₀) (mulUp δ (radius cZ.P.A i))
      have h3 := le_dotUp (cZ.P.A i) β₀
      have h4 := mul_le_mulUp δ (radius cZ.P.A i)
      have h5 := (abs_le.mp (ConZonotope.aux_row_move cZ.P.A β' hδ hβδ i)).2
      rw [hsplit]
      linarith
    · -- the slab's lower end
      have h1 := toReal_le_of_le (heq i).2
      have h2 := subDown_le_sub (dotDown (cZ.P.Ae i) β₀) (mulUp δ (radius cZ.P.Ae i))
      have h3 := dotDown_le (cZ.P.Ae i) β₀
      have h4 := mul_le_mulUp δ (radius cZ.P.Ae i)
      have h5 := (abs_le.mp (ConZonotope.aux_row_move cZ.P.Ae β' hδ hβδ i)).1
      rw [hsplit]
      linarith
    · -- the slab's upper end
      have h1 := toReal_le_of_le (heq i).1
      have h2 := add_le_addUp (dotUp (cZ.P.Ae i) β₀) (mulUp δ (radius cZ.P.Ae i))
      have h3 := le_dotUp (cZ.P.Ae i) β₀
      have h4 := mul_le_mulUp δ (radius cZ.P.Ae i)
      have h5 := (abs_le.mp (ConZonotope.aux_row_move cZ.P.Ae β' hδ hβδ i)).2
      rw [hsplit]
      linarith
  · -- the point: `y = c + G β` since `G β' = y - y₀`
    have := congrFun hβ' i
    simp only [Matrix.mulVec, dotProduct] at this
    have hsum : ∑ j, toReal (cZ.G i j) * (toReal (β₀ j) + β' j)
        = ∑ j, toReal (cZ.G i j) * toReal (β₀ j) + ∑ j, toReal (cZ.G i j) * β' j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    have h2 : ∑ j, toReal (cZ.G i j) * β' j = y i - (toReal (cZ.c i)
        + ∑ j, toReal (cZ.G i j) * toReal (β₀ j)) := this
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
