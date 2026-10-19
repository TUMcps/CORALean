module

public import CORALean.ContSet.Capsule.Float.Operations.ConvHull
public import CORALean.ContSet.Capsule.Float.Theorems.MemConstructOfSplit
public import CORALean.ContSet.Capsule.Float.Theorems.RadiusLe
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Capsule.Float.Theorems.SmulMemSymmetric

@[expose] public section

/-!
# `Capsule.convHull` encloses the hull

The exact layer's argument (`Real.Capsule.convHull_outer`) with `Capsule.radius` in place of the
exact radii: a point `l x + (1 - l) y` of the hull is `c_ + (2l - 1) g_ + w` for the exact
midpoint `c_`, half-difference `g_` and `w = l (x - c) + (1 - l) (y - S.c)`, whose length is at
most the larger radius, because `radius_le` bounds `‖x - c‖₂` for every point of the set, the error
box included. What the exact `c_` and `g_` miss of the stored ones is at most half the gap of the
two roundings per entry (`aux_half_gap_le`), which the two symmetric boxes of the stored box hold.
Outer only, as the exact hull.

## Inputs
* `k` – Newton steps for sqrt
* `C` – first capsule
* `S` – second capsule

## Hypotheses
* none

## Conclusion
* the hull of both capsules lies in `convHull`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A value `x` between the roundings `d ≤ x ≤ u` of the same quantity: half of `x` is within
half the gap of the stored half of `u`. -/
theorem Capsule.aux_half_gap_le {x : ℝ} {u d : 𝕋} (hd : toReal d ≤ x) (hu : x ≤ toReal u) :
    |x / 2 - toReal (half u)| ≤ toReal (half (subUp u d)) := by
  have h₃ := sub_le_subUp u d
  rw [toReal_half, toReal_half]
  rw [abs_of_nonpos (by linarith)]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.convHull_outer (k : ℕ) (C S : Capsule 𝕋 n) :
    Set.linComb C.construct S.construct ⊆ (C.convHull k S).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, y, hy, l, ⟨hl0, hl1⟩, rfl⟩
  have h₁ := Capsule.radius_le k C hx
  have h₂ := Capsule.radius_le k S hy
  have ht : 2 * l - 1 ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  refine Capsule.mem_construct_of_split _ ht
    (w := l • (x - toRealVec C.c) + (1 - l) • (y - toRealVec S.c)) ?_ ?_
  · -- the two offsets, each within the larger radius
    show _ ≤ toReal (maximum (C.radius k) (S.radius k))
    refine (norm₂_add_le _ _).trans ?_
    rw [norm₂_smul, norm₂_smul, abs_of_nonneg hl0, abs_of_nonneg (by linarith), toReal_maximum]
    have a₁ := mul_le_mul_of_nonneg_left (h₁.trans (le_max_left _ (toReal (S.radius k)))) hl0
    have a₂ := mul_le_mul_of_nonneg_left (h₂.trans (le_max_right (toReal (C.radius k)) _))
      (by linarith : 0 ≤ 1 - l)
    nlinarith
  · -- the center's and the generator's half-gaps
    have hc := Capsule.smul_mem_symmetric (t := 1)
      (m := fun i => half (subUp (addUp (C.c i) (S.c i)) (addDown (C.c i) (S.c i))))
      (δ := fun i => (toReal (C.c i) + toReal (S.c i)) / 2 - toReal (half (addUp (C.c i) (S.c i))))
      (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩) fun i =>
        Capsule.aux_half_gap_le (addDown_le_add _ _) (add_le_addUp _ _)
    have hg := Capsule.smul_mem_symmetric (t := 2 * l - 1)
      (m := fun i => half (subUp (subUp (C.c i) (S.c i)) (subDown (C.c i) (S.c i))))
      (δ := fun i => (toReal (C.c i) - toReal (S.c i)) / 2 - toReal (half (subUp (C.c i) (S.c i))))
      ht fun i => Capsule.aux_half_gap_le (subDown_le_sub _ _) (sub_le_subUp _ _)
    show _ ∈ ((Interval.symmetric fun i =>
        half (subUp (addUp (C.c i) (S.c i)) (addDown (C.c i) (S.c i)))).plus
      (Interval.symmetric fun i =>
        half (subUp (subUp (C.c i) (S.c i)) (subDown (C.c i) (S.c i))))).construct
    convert Interval.plus_outer _ _ ⟨_, hc, _, hg, rfl⟩ using 1
    funext i
    simp only [Capsule.convHull, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      toRealVec]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
