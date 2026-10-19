module

public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.IneqsContainBallSound
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff
public import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach

@[expose] public section

/-!
# A passed `ConZonotope.interiorCert` puts a box of points in the nominal set

A point `y` within `B` of `y₀ = c + G β₀` is `y₀ + G β'` for coefficients `β'` of size at most `δ`
(`Zonotope.ballCert_reach`). The coefficients `β₀ + β'` stay in the unit box and in every row of
the constraint polytope, since each row moves by at most `δ` times its absolute sum, which the
check has charged.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.box_subset {cZ : ConZonotope 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cZ.h n} {β₀ : Vec 𝕋 cZ.h}
    {δ B : 𝕋} (hc : cZ.interiorCert H β₀ δ B = true) (y : Vec ℝ n)
    (hy : ∀ i, |y i - (toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j))| ≤ toReal B) :
    y ∈ nominalSet cZ := by -- --- PROOF ---
  simp only [ConZonotope.interiorCert, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hδ0, hbox⟩, hineq⟩, hme⟩, hball⟩ := hc
  have hδ : 0 ≤ toReal δ := by simpa [toReal_zero] using toReal_le_of_le hδ0
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hball
  obtain ⟨β', hβ', hβδ⟩ := hreach (fun i => y i - (toReal (cZ.c i)
    + ∑ j, toReal (cZ.G j i) * toReal (β₀ j))) hy
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
    rw [HPolytope.mem_nominal_iff]
    have hsplit : ∀ {m : ℕ} (M : Mat 𝕋 m cZ.h) (i : Fin m),
        (toRealMat M *ᵥ fun j => toReal (β₀ j) + β' j) i
          = ∑ j, toReal (M i j) * toReal (β₀ j) + (toRealMat M *ᵥ β') i := by
      intro m M i
      simp only [Matrix.mulVec, dotProduct, toRealMat]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- the inequality rows; there is no equality row
    refine ⟨fun i => ?_, fun i => absurd i.isLt (by omega)⟩
    exact HPolytope.ineqsContainBall_sound hineq hδ (fun j => by simpa using hβδ j) i
  · -- the point: `y = c + G β` since `G β' = y - y₀`
    have := congrFun hβ' i
    simp only [Matrix.mulVec, dotProduct] at this
    have hsum : ∑ j, toReal (cZ.G j i) * (toReal (β₀ j) + β' j)
        = ∑ j, toReal (cZ.G j i) * toReal (β₀ j) + ∑ j, toReal (cZ.G j i) * β' j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    have h2 : ∑ j, toReal (cZ.G j i) * β' j = y i - (toReal (cZ.c i)
        + ∑ j, toReal (cZ.G j i) * toReal (β₀ j)) := this
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
