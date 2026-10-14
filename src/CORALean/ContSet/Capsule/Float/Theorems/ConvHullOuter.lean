module

public import CORALean.ContSet.Capsule.Float.Operations.ConvHull
public import CORALean.ContSet.Capsule.Real.Theorems.ConvHullOuter
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe

@[expose] public section

/-!
# `Capsule.convHull` encloses the hull

The exact layer's `convHull_outer` at the nominal capsules gives the segments inside the exact
hull capsule; `construct_subset_of_dist_le` moves that to the stored one. Its centre and generator
are each at most `normUp` of the half-gaps away (`aux_half_gap_le`), and the stored radius adds
both to the larger rounded-up radius. Outer only, as the exact hull.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A value `x` between the roundings `d ≤ x ≤ u` of the same quantity: half of `x` is within
half the gap of the stored half of `u`. -/
theorem Capsule.aux_half_gap_le {x : ℝ} {u d : 𝕋} (hd : toReal d ≤ x) (hu : x ≤ toReal u) :
    |x / 2 - toReal (half u)| ≤ |toReal (half (subUp u d))| := by -- --- PROOF ---
  have h₃ := sub_le_subUp u d
  rw [toReal_half, toReal_half]
  refine le_trans ?_ (le_abs_self _)
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem Capsule.aux_radius_le (k : ℕ) (C : Capsule 𝕋 n) :
    C.nominal.radius ≤ toReal (C.radius k) := by -- --- PROOF ---
  have h₂ : ‖toRealVec C.g‖₂ ≤ toReal (normUp k C.g) :=
    norm₂_le_normUp k fun j => le_rfl
  have h₃ := add_le_addUp (normUp k C.g) C.r
  change ‖toRealVec C.g‖₂ + toReal C.r ≤ toReal (addUp (normUp k C.g) C.r)
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.convHull_outer (k : ℕ) (C S : Capsule 𝕋 n) :
    Set.linComb C.construct S.construct ⊆ (C.convHull k S).construct := by -- --- PROOF ---
  intro z hz
  -- the exact hull capsule holds the segments
  have hK := CORALean.Real.Capsule.convHull_outer C.nominal S.nominal hz
  refine CORALean.Real.Capsule.construct_subset_of_dist_le (C := C.nominal.convHull S.nominal)
    ?_ hK
  -- the centre's and the generator's half-gaps, rounded up
  set gc := normUp k fun i => half (subUp (addUp (C.c i) (S.c i)) (addDown (C.c i) (S.c i)))
  set gg := normUp k fun i => half (subUp (subUp (C.c i) (S.c i)) (subDown (C.c i) (S.c i)))
  have hc : ‖(C.nominal.convHull S.nominal).c - (Capsule.convHull k C S).nominal.c‖₂ ≤
      toReal gc := by
    refine norm₂_le_normUp k fun j => ?_
    have h := Capsule.aux_half_gap_le (x := toReal (C.c j) + toReal (S.c j))
      (addDown_le_add (C.c j) (S.c j)) (add_le_addUp (C.c j) (S.c j))
    have e : (C.nominal.convHull S.nominal).c j - toReal (half (addUp (C.c j) (S.c j))) =
        (toReal (C.c j) + toReal (S.c j)) / 2 - toReal (half (addUp (C.c j) (S.c j))) := by
      show (1 / 2 : ℝ) * (toReal (C.c j) + toReal (S.c j)) - _ = _
      ring
    show |(C.nominal.convHull S.nominal).c j - toReal (half (addUp (C.c j) (S.c j)))| ≤ _
    rw [e]; exact h
  have hg : ‖(C.nominal.convHull S.nominal).g - (Capsule.convHull k C S).nominal.g‖₂ ≤
      toReal gg := by
    refine norm₂_le_normUp k fun j => ?_
    -- the same, for the difference
    have h := Capsule.aux_half_gap_le (x := toReal (C.c j) - toReal (S.c j))
      (subDown_le_sub (C.c j) (S.c j)) (sub_le_subUp (C.c j) (S.c j))
    have e : (C.nominal.convHull S.nominal).g j - toReal (half (subUp (C.c j) (S.c j))) =
        (toReal (C.c j) - toReal (S.c j)) / 2 - toReal (half (subUp (C.c j) (S.c j))) := by
      show toReal (C.c j) - (1 / 2 : ℝ) * (toReal (C.c j) + toReal (S.c j)) - _ = _
      ring
    show |(C.nominal.convHull S.nominal).g j - toReal (half (subUp (C.c j) (S.c j)))| ≤ _
    rw [e]; exact h
  -- the stored radius adds both gaps to the larger rounded-up radius
  have hr₁ := Capsule.aux_radius_le k C
  have hr₂ := Capsule.aux_radius_le k S
  have s₁ := add_le_addUp (maximum (C.radius k) (S.radius k)) (addUp gc gg)
  have s₂ := add_le_addUp gc gg
  have hm : max C.nominal.radius S.nominal.radius ≤
      toReal (maximum (C.radius k) (S.radius k)) := by
    rw [toReal_maximum]; exact max_le_max hr₁ hr₂
  show _ + _ + max C.nominal.radius S.nominal.radius ≤ toReal (addUp _ _)
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
