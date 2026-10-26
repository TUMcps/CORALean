module

public import CORALean.ContSet.Capsule.Float.Operations.Plus
public import CORALean.ContSet.Capsule.Float.Theorems.MemConstructOfSplit
public import CORALean.ContSet.Capsule.Real.Theorems.PlusOuterKeepLeft
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Capsule.Float.Theorems.Basic

@[expose] public section

/-!
# `Capsule.plus` encloses the sum

Each operand's point is a point of its nominal capsule plus a point of its box. The exact layer's
`plus_outer_keep_left` puts the sum of the nominal points in the capsule that keeps one generator,
with the center added exactly: a point `(c₁ + c₂) + t g + w` with `‖w‖₂` below the radius, which
the stored radius rounds up. What that point and the two box points miss of the stored
`c + t g + w` is the two box points plus `c₁ + c₂ - c`, the center's rounding, and the stored box
is their sum.

## Inputs
* `k` – Newton steps for sqrt
* `C₁` – first capsule
* `C₂` – second capsule

## Hypotheses
* none

## Conclusion
* the Minkowski sum lies in `plus`
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The kept generator `g`, the shorter one `g'` folded into the radius: a point of the exact
keep-left capsule plus the two box points lies in the stored capsule. -/
private theorem Capsule.aux_plus_branch (k : ℕ) (C₁ C₂ : Capsule 𝕋 n) {g g' : Vec 𝕋 n}
    {y e : Vec ℝ n} (hy : y ∈ (Real.Capsule.mk (toRealVec C₁.c + toRealVec C₂.c) (toRealVec g)
      (toReal C₁.r + toReal C₂.r + Real.sqrt (∑ i, toReal (g' i) ^ 2))).construct)
    (he : e ∈ (C₁.I_error.plus C₂.I_error).construct) : -- --- CONCL ---
    y + e ∈ (Capsule.mk (fun i => addDown (C₁.c i) (C₂.c i)) g
      (addUp (addUp C₁.r C₂.r) (normUp k g')) ((C₁.I_error.plus C₂.I_error).plus
        (Interval.residual (fun i => addDown (C₁.c i) (C₂.c i)) (fun i => addUp (C₁.c i) (C₂.c i))
          (fun i => addDown (C₁.c i) (C₂.c i))))).construct := by -- --- PROOF ---
  obtain ⟨t, ht, w, hw, rfl⟩ := Capsule.exists_split_of_mem hy
  -- the radius rounded up, and the center's rounding
  have hg : ‖toRealVec g'‖₂ ≤ toReal (normUp k g') := norm₂_le_normUp k fun j => le_rfl
  have s₁ := add_le_addUp C₁.r C₂.r
  have s₂ := add_le_addUp (addUp C₁.r C₂.r) (normUp k g')
  have hres := Interval.sub_mem_residual (stored := fun i => addDown (C₁.c i) (C₂.c i))
    (x := toRealVec C₁.c + toRealVec C₂.c)
    (lo := fun i => addDown (C₁.c i) (C₂.c i)) (hi := fun i => addUp (C₁.c i) (C₂.c i))
    fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  refine Capsule.mem_construct_of_split _ ht (w := w) ?_ ?_
  · show ‖w‖₂ ≤ toReal (addUp (addUp C₁.r C₂.r) (normUp k g'))
    have : ‖w‖₂ ≤ toReal C₁.r + toReal C₂.r + ‖toRealVec g'‖₂ := hw
    linarith
  · refine Interval.plus_outer _ _ ⟨e, he, _, hres, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toRealVec]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.plus_outer (k : ℕ) (C₁ C₂ : Capsule 𝕋 n) : -- --- CONCL ---
    C₁.construct + C₂.construct ⊆ (C₁.plus k C₂).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨y₁, h₁, e₁, he₁, rfl⟩, _, ⟨y₂, h₂, e₂, he₂, rfl⟩, rfl⟩
  have he : e₁ + e₂ ∈ (C₁.I_error.plus C₂.I_error).construct :=
    Interval.plus_outer _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩
  have hsum : y₁ + e₁ + (y₂ + e₂) = (y₁ + y₂) + (e₁ + e₂) := by abel
  show y₁ + e₁ + (y₂ + e₂) ∈ _
  rw [hsum]
  unfold Capsule.plus
  dsimp only
  split_ifs
  · -- the first generator is kept
    exact Capsule.aux_plus_branch k C₁ C₂
      (CORALean.Real.Capsule.plus_outer_keep_left C₁.nominal C₂.nominal h₁ h₂) he
  · -- the second generator is kept: the same with the operands swapped
    have hK := CORALean.Real.Capsule.plus_outer_keep_left C₂.nominal C₁.nominal h₂ h₁
    rw [add_comm y₂ y₁] at hK
    refine Capsule.aux_plus_branch (g' := C₁.g) k C₁ C₂ ?_ he
    have hc : toRealVec C₂.c + toRealVec C₁.c = toRealVec C₁.c + toRealVec C₂.c := add_comm _ _
    have hr : toReal C₂.r + toReal C₁.r = toReal C₁.r + toReal C₂.r := add_comm _ _
    simp only [Capsule.nominal, hc, hr] at hK
    exact hK

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
