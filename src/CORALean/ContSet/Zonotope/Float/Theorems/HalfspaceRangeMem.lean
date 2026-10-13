import CORALean.ContSet.Zonotope.Float.Operations.HalfspaceRange
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

/-!
# `nᵀx − d` of a point of a float zonotope lies in `halfspaceRange`

A point is `c + ∑ⱼ βⱼgⱼ + e`: `nᵀc − d` is within its directed brackets, `|∑ⱼ βⱼ nᵀgⱼ|` is at
most `∑ⱼ |nᵀgⱼ| ≤ ρ`, and each `nᵢeᵢ` is between the corner products (`mul_between_corners`).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.halfspaceRange_mem (nv : Vec 𝕋 n) (d : 𝕋) {Z : Zonotope (Vec 𝕋 n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) :
    toReal (Z.halfspaceRange nv d).1 ≤ toRealVec nv ⬝ᵥ x - toReal d ∧
      toRealVec nv ⬝ᵥ x - toReal d ≤ toReal (Z.halfspaceRange nv d).2 := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hx
  obtain ⟨β, hβ, ha⟩ := Zonotope.mem_nominalSet_iff.mp ha
  show toReal _ ≤ toRealVec nv ⬝ᵥ (a + e) - toReal d ∧ toRealVec nv ⬝ᵥ (a + e) - toReal d ≤ _
  -- the generators' part, `|∑ⱼ βⱼ nᵀgⱼ| ≤ ρ`
  set s : Fin Z.h → ℝ := fun j => ∑ k, toReal (nv k) * toReal (Z.G j k) with hs
  have hsj : ∀ j, |s j| ≤ toReal (maximum (dotUp nv (Z.G j)) (neg (dotDown nv (Z.G j)))) :=
    fun j => by
      rw [toReal_maximum, toReal_neg]
      have h1 := dotDown_le nv (Z.G j)
      have h2 := le_dotUp nv (Z.G j)
      have h3 := le_max_right (toReal (dotUp nv (Z.G j))) (-toReal (dotDown nv (Z.G j)))
      exact abs_le.mpr ⟨by linarith, le_trans h2 (le_max_left _ _)⟩
  have hgen : |∑ j, β j * s j| ≤ toReal (sumUp fun j =>
      maximum (dotUp nv (Z.G j)) (neg (dotDown nv (Z.G j)))) :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hβ j)).trans (hsj j)).trans (sum_le_sumUp _))
  -- the box's part, term by term between the corners
  have hbox : ∀ i, toReal (Interval.mulLo (nv i) (nv i) (Z.E.inf i) (Z.E.sup i))
      ≤ toReal (nv i) * e i ∧ toReal (nv i) * e i
        ≤ toReal (Interval.mulHi (nv i) (nv i) (Z.E.inf i) (Z.E.sup i)) := fun i =>
    Interval.mul_between_corners le_rfl le_rfl (he i).1 (he i).2
  have hbLo := (Finset.sum_le_sum fun i _ => (hbox i).1).trans' (sumDown_le_sum _)
  have hbHi := (Finset.sum_le_sum fun i _ => (hbox i).2).trans (sum_le_sumUp _)
  -- `nᵀ(a + e) − d = (nᵀc − d) + ∑ⱼ βⱼ sⱼ + ∑ᵢ nᵢeᵢ`
  have hsplit : toRealVec nv ⬝ᵥ (a + e) - toReal d = (∑ k, toReal (nv k) * toReal (Z.c k)
      - toReal d) + ∑ j, β j * s j + ∑ i, toReal (nv i) * e i := by
    simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, toRealVec, hs,
      Finset.mul_sum]
    -- the generators' double sum, regrouped by generator
    rw [Finset.sum_comm (f := fun x y => toReal (nv x) * (toReal (Z.G y x) * β y))]
    have : ∀ x y, toReal (nv x) * (toReal (Z.G y x) * β y) = β y * (toReal (nv x) *
        toReal (Z.G y x)) := fun _ _ => by ring
    simp only [this]
    ring
  rw [hsplit]
  -- every rounding of the two ends, then the bounds add up
  have hcLo := dotDown_le nv Z.c
  have hcHi := le_dotUp nv Z.c
  have h1 := subDown_le_sub (dotDown nv Z.c) d
  have h2 := sub_le_subUp (dotUp nv Z.c) d
  set ρ := sumUp fun j => maximum (dotUp nv (Z.G j)) (neg (dotDown nv (Z.G j)))
  have h3 := subDown_le_sub (subDown (dotDown nv Z.c) d) ρ
  have h4 := add_le_addUp (subUp (dotUp nv Z.c) d) ρ
  have h5 := addDown_le_add (subDown (subDown (dotDown nv Z.c) d) ρ)
    (sumDown fun i => Interval.mulLo (nv i) (nv i) (Z.E.inf i) (Z.E.sup i))
  have h6 := add_le_addUp (addUp (subUp (dotUp nv Z.c) d) ρ)
    (sumUp fun i => Interval.mulHi (nv i) (nv i) (Z.E.inf i) (Z.E.sup i))
  have hg := abs_le.mp hgen
  simp only [Zonotope.halfspaceRange]
  constructor <;> linarith [hg.1, hg.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
