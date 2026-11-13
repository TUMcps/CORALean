module

public import CORALean.HybridDynamics.Operations.ZonoGirardMemberFloat
public import CORALean.HybridDynamics.Theorems.ZonoGirardBoxFloatMem
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter

@[expose] public section

/-!
# `Location.zonoGirardMemberFloat` holds every state that meets the guard, for any basis

A state `x` of a reach set on the hyperplane is `B (Bᵀ x) + (I - B Bᵀ) x`, for any real matrix
`B`. The first term is in `B zonotope(I)` (`zonoGirardBoxFloat_mem`), the second in the box
`[-r, r]` (the defect box holds `I - B Bᵀ`, the joined boxes of the reach sets hold `x`). Where the
defect box is the zero matrix the second term is zero. No orthogonality is assumed.

## Inputs
* `B` – basis
* `R₀` – initial zonotope
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset
* `R` – reach set
* `x` – state

## Hypotheses
* `hR` – the reach set is among the given ones
* `hx` – state lies in the reach set
* `hg` – state lies on the guard

## Conclusion
* state lies in the member
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `I - B Bᵀ` of the real reading of `B` lies in the box: each entry is the identity minus a
dot product, which the directed products bracket. -/
private theorem Location.aux_orthDefect_mem (B : Mat 𝕋 n n) : -- --- CONCL ---
    (1 - Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ) ∈
      (Location.step_orthDefect B).toSet := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hprod : (Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ) i j =
      ∑ k, toReal (B i k) * toReal (B j k) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Scalar.toRealMat_apply]
    rfl
  have he : toReal (if i = j then (one : 𝕋) else zero) = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    by_cases h : i = j
    · subst h; simp [toReal_one]
    · simp [h, toReal_zero, Matrix.one_apply_ne h]
  have hd := dotDown_le (B i) (B j)
  have hu := le_dotUp (B i) (B j)
  have h1 := subDown_le_sub (if i = j then (one : 𝕋) else zero) (dotUp (B i) (B j))
  have h2 := sub_le_subUp (if i = j then (one : 𝕋) else zero) (dotDown (B i) (B j))
  rw [he] at h1 h2
  simp only [Matrix.sub_apply, hprod]
  constructor
  · exact le_trans h1 (by linarith)
  · exact le_trans (by linarith) h2


-- =======================================  MAIN THEOREM  ======================================= --

/-- A state in a reach set and on the hyperplane lies in the member, for every basis. -/
theorem Location.zonoGirardMemberFloat_mem (B : Mat 𝕋 n n) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋)
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.toSet)
    (hg : x ⬝ᵥ toRealVec nv = toReal γ) : -- --- CONCL ---
    x ∈ (Location.zonoGirardMemberFloat B R₀ Rs nv γ).toSet := by -- --- PROOF ---
  have hT : Scalar.toRealMat Bᵀ = (Scalar.toRealMat B)ᵀ := by
    ext a b
    simp [Scalar.toRealMat_apply]
  -- `B (Bᵀ x)` is in `B zonotope(I)`
  have h2 := Location.zonoGirardBoxFloat_mem B R₀ Rs nv γ hR hx hg
  have hmain : Scalar.toRealMat B *ᵥ (Scalar.toRealMat Bᵀ *ᵥ x) ∈
      (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
        (Location.zonoGirardBoxFloat B R₀ Rs nv γ).zonotope).toSet :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B _
      (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
        (Interval.zonotope_contains _ h2)))
  have hsplit : x = Scalar.toRealMat B *ᵥ (Scalar.toRealMat Bᵀ *ᵥ x) +
      (1 - Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ) *ᵥ x := by
    rw [hT, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  unfold Location.zonoGirardMemberFloat
  dsimp only
  split_ifs with hz
  · -- the defect box is the zero matrix: the second term is zero
    have hD : (1 - Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ) = 0 := by
      -- every entry of the defect box is `[0, 0]`
      have hm := Location.aux_orthDefect_mem B
      rw [Interval.mem_mat_iff] at hm
      ext i j
      have hi : i ∈ List.finRange n := List.mem_finRange i
      have hj : j ∈ List.finRange n := List.mem_finRange j
      simp only [List.all_eq_true, Bool.and_eq_true] at hz
      obtain ⟨h1, h2⟩ := hz i hi j hj
      have a1 := SoundFloatArithmetic.toReal_le_of_le h1
      have a2 := SoundFloatArithmetic.toReal_le_of_le h2
      rw [SoundFloatArithmetic.toReal_zero] at a1 a2
      have := hm i j
      simp only [Matrix.zero_apply]
      linarith [this.1, this.2]
    rw [hD, Matrix.zero_mulVec, add_zero] at hsplit
    rw [hsplit]
    exact hmain
  · -- the defect term, in the box `[-r, r]`
    set E := Location.step_orthDefect B
    set Xi := (Rs.map Zonotope.interval).foldl Interval.or R₀.interval
    -- the state lies in the joined boxes of the reach sets
    have hX : x ∈ Xi.toSet := by
      have hfold : ∀ (Is : List (Interval (Vec 𝕋 n))) (J : Interval (Vec 𝕋 n)) (y : Vec ℝ n),
          (y ∈ J.toSet ∨ ∃ I ∈ Is, y ∈ I.toSet) → y ∈ (Is.foldl Interval.or J).toSet := by
        intro Is
        induction Is with
        | nil => exact fun J y h => h.resolve_right (by simp)
        | cons I Is ih =>
          intro J y h
          rw [List.foldl_cons]
          refine ih _ y ?_
          rcases h with hJ | ⟨I', hI', hy⟩
          · exact Or.inl (Interval.or_outer J I (Or.inl hJ))
          · rcases List.mem_cons.mp hI' with rfl | hI'
            · exact Or.inl (Interval.or_outer J I' (Or.inr hy))
            · exact Or.inr ⟨I', hI', hy⟩
      refine hfold _ _ x ?_
      rcases List.mem_cons.mp hR with rfl | hR'
      · exact Or.inl (Zonotope.interval_contains _ hx)
      · exact Or.inr ⟨_, List.mem_map.mpr ⟨R, hR', rfl⟩, Zonotope.interval_contains _ hx⟩
    -- a number between two ends is at most the larger of their absolute values
    have key : ∀ l u d : ℝ, l ≤ d → d ≤ u → |d| ≤ max |l| |u| := fun l u d h1 h2 =>
      abs_le.mpr ⟨by linarith [neg_abs_le l, le_max_left |l| |u|],
        by linarith [le_abs_self u, le_max_right |l| |u|]⟩
    -- the entries of `I - B Bᵀ` lie in the defect box
    have hD := Interval.mem_mat_iff.mp (Location.aux_orthDefect_mem B)
    -- the box `[-r, r]` holds `(I - B Bᵀ) x`
    set D := (1 - Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ) with hDdef
    have hbox : D *ᵥ x ∈ (⟨-(fun i => sumUp fun j =>
        mulUp (maximum (absolute (E.inf i j)) (absolute (E.sup i j)))
          (maximum (absolute (Xi.inf j)) (absolute (Xi.sup j)))),
        (fun i => sumUp fun j =>
        mulUp (maximum (absolute (E.inf i j)) (absolute (E.sup i j)))
          (maximum (absolute (Xi.inf j)) (absolute (Xi.sup j))))⟩ :
          Interval (Vec 𝕋 n)).toSet := by
      refine Interval.mem_vec_iff.mpr fun i => ?_
      -- `|(D x)_i| ≤ Σ_j |D_ij| |x_j| ≤ r_i`
      have hbound : |(D *ᵥ x) i| ≤ toReal (sumUp fun j =>
          mulUp (maximum (absolute (E.inf i j)) (absolute (E.sup i j)))
            (maximum (absolute (Xi.inf j)) (absolute (Xi.sup j)))) := by
        refine le_trans ?_ (sum_le_sumUp _)
        -- the triangle inequality, term by term
        rw [Matrix.mulVec, dotProduct]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        refine le_trans ?_ (SoundFloatArithmetic.mul_le_mulUp _ _)
        have hxj := Interval.mem_vec_iff.mp hX j
        have hDij := hD i j
        refine mul_le_mul ?_ ?_ (abs_nonneg _) ?_
        · rw [toReal_maximum, toReal_absolute, toReal_absolute]
          exact key _ _ _ hDij.1 hDij.2
        · rw [toReal_maximum, toReal_absolute, toReal_absolute]
          exact key _ _ _ hxj.1 hxj.2
        · rw [toReal_maximum, toReal_absolute, toReal_absolute]
          exact le_max_of_le_left (abs_nonneg _)
      simp only [Pi.neg_apply, toReal_neg']
      exact ⟨by linarith [(abs_le.mp hbound).1], (abs_le.mp hbound).2⟩
    -- the sum of the two terms is in the sum of the two sets
    have hp := Zonotope.plus_outer _ _ (Set.add_mem_add hmain (Interval.zonotope_contains _ hbox))
    rwa [← hsplit] at hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
