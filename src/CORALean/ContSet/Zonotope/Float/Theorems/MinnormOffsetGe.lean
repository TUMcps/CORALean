module

public import CORALean.ContSet.Zonotope.Float.Operations.MinnormOffset
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The rounded offset bounds every ball around the center

If `Zonotope.minnormOffset` returns `U` at a vector `C`, every Euclidean ball around the center
that lies in the zonotope the stored floats describe has radius at most `U`. The vector `C` is
whatever `facetNormal` rounded to, and need not be a normal: for any nonzero `u`, a point
`c + r u / ‖u‖₂` of the ball is `c + Σ βⱼ gⱼ` with `|βⱼ| ≤ 1`, so `r ‖u‖₂ = u·(Σ βⱼ gⱼ)` is at
most `Σⱼ |u·gⱼ|`, the exact offset's numerator. Each rounding goes the way that enlarges the bound.

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m` and `contSet/@zonotope/polytope.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnormOffset_ge (p : ℕ) (Z : Zonotope (Vec 𝕋 (n + 1))) (S : Fin n → Fin Z.h)
    (r : ℝ) (hr : 0 ≤ r)
    (hball : ∀ y : Vec ℝ (n + 1), y ⬝ᵥ y ≤ r ^ 2 →
      toRealVec Z.c + y ∈ nominalSet Z) : -- --- STMT ---
    ∀ U ∈ Z.minnormOffset p S,
      r ≤ toReal U := by -- --- PROOF ---
  intro U (hU : Z.minnormOffset p S = some U)
  unfold Zonotope.minnormOffset at hU
  dsimp only at hU
  split_ifs at hU with hl
  rw [Option.some.injEq] at hU
  subst hU
  -- the vector, its length from below, and the length itself
  set C := Z.facetNormal S with hC
  set u : Vec ℝ (n + 1) := toRealVec C with hu
  have hlen : 0 < toReal (sqrtDown p (dotDown C C)) := by
    have := toReal_lt_of_ltStrict hl
    rwa [toReal_zero] at this
  have hle : toReal (sqrtDown p (dotDown C C)) ≤ Real.sqrt (u ⬝ᵥ u) :=
    le_trans (sqrtDown_le p _) (Real.sqrt_le_sqrt (dotDown_le C C))
  have hs : 0 < Real.sqrt (u ⬝ᵥ u) := lt_of_lt_of_le hlen hle
  have huu : 0 < u ⬝ᵥ u := Real.sqrt_pos.mp hs
  have hss : Real.sqrt (u ⬝ᵥ u) * Real.sqrt (u ⬝ᵥ u) = u ⬝ᵥ u := Real.mul_self_sqrt huu.le
  generalize Real.sqrt (u ⬝ᵥ u) = s at hle hs hss
  -- the point of the ball along `u`, at distance `r` from the center
  set y : Vec ℝ (n + 1) := (r / s) • u with hy
  have hyy : y ⬝ᵥ y ≤ r ^ 2 := by
    rw [hy, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    refine le_of_eq ?_
    rw [← hss]
    field_simp
  have huy : u ⬝ᵥ y = r * s := by
    rw [hy, dotProduct_smul, smul_eq_mul]
    rw [← hss]
    field_simp
  -- it is a nominal point: `y` is a combination of the generators
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp (hball y hyy)
  have hyi : ∀ i, y i = ∑ j, toReal (Z.G j i) * β j := fun i => by
    have := hx i
    simp only [Pi.add_apply, toRealVec] at this
    linarith
  -- so `u·y` is at most the sum of `|u·gⱼ|`
  have hdot : u ⬝ᵥ y ≤ ∑ j, |∑ i, u i * toReal (Z.G j i)| := by
    have : u ⬝ᵥ y = ∑ j, β j * ∑ i, u i * toReal (Z.G j i) := by
      simp only [dotProduct, hyi, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    refine Finset.sum_le_sum fun j _ => ?_
    calc β j * ∑ i, u i * toReal (Z.G j i) ≤ |β j * ∑ i, u i * toReal (Z.G j i)| := le_abs_self _
      _ = |β j| * |∑ i, u i * toReal (Z.G j i)| := abs_mul _ _
      _ ≤ 1 * |∑ i, u i * toReal (Z.G j i)| :=
          mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg _)
      _ = |∑ i, u i * toReal (Z.G j i)| := one_mul _
  -- each term is under the rounded magnitude, the sum under the rounded sum
  have hterm : ∀ j, |∑ i, u i * toReal (Z.G j i)|
      ≤ toReal (maximum (dotUp C (Z.G j)) (neg (dotDown C (Z.G j)))) := fun j => by
    rw [toReal_maximum, toReal_neg,
      show ∑ i, u i * toReal (Z.G j i) = ∑ k, toReal (C k) * toReal (Z.G j k) from rfl]
    have h1 := le_dotUp C (Z.G j)
    have h2 := dotDown_le C (Z.G j)
    rw [abs_le]
    have h3 := le_max_left (toReal (dotUp C (Z.G j))) (-toReal (dotDown C (Z.G j)))
    have h4 := le_max_right (toReal (dotUp C (Z.G j))) (-toReal (dotDown C (Z.G j)))
    exact ⟨by linarith, by linarith⟩
  -- the rounded sum of the generators' magnitudes along `C`
  set Δu := sumUp fun υ => maximum (dotUp C (Z.G υ)) (neg (dotDown C (Z.G υ)))
  have hΔ : r * s ≤ toReal Δu :=
    huy ▸ le_trans hdot (le_trans (Finset.sum_le_sum fun j _ => hterm j) (sum_le_sumUp _))
  have hΔ0 : 0 ≤ toReal Δu :=
    le_trans (mul_nonneg hr hs.le) hΔ
  -- divide: by the true length, then by its lower bound, then round the quotient up
  calc r ≤ toReal Δu / s := (le_div_iff₀ hs).mpr hΔ
    _ ≤ toReal Δu / toReal (sqrtDown p (dotDown C C)) := div_le_div_of_nonneg_left hΔ0 hlen hle
    _ ≤ _ := div_le_divUp _ _ hlen

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
