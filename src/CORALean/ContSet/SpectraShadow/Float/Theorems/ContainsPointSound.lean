import CORALean.ContSet.SpectraShadow.Float.Operations.ContainsPoint
import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
import CORALean.ContSet.SpectraShadow.Float.Theorems.PosSemidefOfDiagDominant

/-!
# A `true` from `SpectraShadow.containsPoint` proves membership

Read as reals, the stored matrices are symmetric, so the combination at `β` is; each of its
entries lies between the roundings the test compared, so it is diagonally dominant and positive
semidefinite (`SpectraShadow.posSemidef_of_diagDominant`). The point `c + G β` is then in the
nominal shadow, and the remainder `p - c - G β` in the error box.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An entry of the combination at `β`, as a sum of stored floats read as reals. -/
theorem SpectraShadow.aux_entry (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (β : Vec 𝕋 S.m) (i j : Fin S.k) :
    (toRealMat S.A₀ + ∑ l, toRealVec β l • toRealMat (S.A l)) i j
      = toReal (S.A₀ i j) + ∑ l, toReal (β l) * toReal (S.A l i j) := by
  simp [Matrix.add_apply, Matrix.sum_apply, toRealMat, toRealVec]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.containsPoint_sound {S : SpectraShadow 𝕋 (Vec 𝕋 n)} {p : Vec 𝕋 n}
    {β : Vec 𝕋 S.m} (h : S.containsPoint p β = true) :
    toRealVec p ∈ S.construct := by -- --- PROOF ---
  simp only [SpectraShadow.containsPoint, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hsym, hdom⟩, hbox⟩ := h
  set M := toRealMat S.A₀ + ∑ l, toRealVec β l • toRealMat (S.A l) with hM
  -- every entry between its two roundings
  have hlo : ∀ i j, toReal (addDown (S.A₀ i j) (dotDown β fun l => S.A l i j)) ≤ M i j :=
    fun i j => by
      rw [hM, SpectraShadow.aux_entry]
      linarith [addDown_le_add (S.A₀ i j) (dotDown β fun l => S.A l i j),
        dotDown_le β fun l => S.A l i j]
  have hhi : ∀ i j, M i j ≤ toReal (addUp (S.A₀ i j) (dotUp β fun l => S.A l i j)) :=
    fun i j => by
      rw [hM, SpectraShadow.aux_entry]
      linarith [add_le_addUp (S.A₀ i j) (dotUp β fun l => S.A l i j),
        le_dotUp β fun l => S.A l i j]
  -- the stored matrices are symmetric, so the combination is
  have hMsym : ∀ i j, M j i = M i j := fun i j => by
    rw [hM, SpectraShadow.aux_entry, SpectraShadow.aux_entry]
    have e₀ : toReal (S.A₀ j i) = toReal (S.A₀ i j) :=
      le_antisymm (toReal_le_of_le (hsym j i).1) (toReal_le_of_le (hsym i j).1)
    have eₗ : ∀ l, toReal (S.A l j i) = toReal (S.A l i j) := fun l =>
      le_antisymm (toReal_le_of_le ((hsym j i).2 l)) (toReal_le_of_le ((hsym i j).2 l))
    simp only [e₀, eₗ]
  -- and diagonally dominant, row by row
  have hMdom : ∀ i, ∑ j, (if j = i then 0 else |M i j|) ≤ M i i := fun i => by
    refine le_trans ?_ (le_trans (toReal_le_of_le (hdom i)) (hlo i i))
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    by_cases hj : j = i
    · simp [hj, toReal_zero]
    · simp only [hj, if_false, toReal_maximum, toReal_neg]
      have m₁ := le_max_left (toReal (addUp (S.A₀ i j) (dotUp β fun l => S.A l i j)))
        (-toReal (addDown (S.A₀ i j) (dotDown β fun l => S.A l i j)))
      have m₂ := le_max_right (toReal (addUp (S.A₀ i j) (dotUp β fun l => S.A l i j)))
        (-toReal (addDown (S.A₀ i j) (dotDown β fun l => S.A l i j)))
      have l₁ := hlo i j
      have h₁ := hhi i j
      exact abs_le'.mpr ⟨by linarith, by linarith⟩
  have hPSD := SpectraShadow.posSemidef_of_diagDominant M hMsym hMdom
  -- the nominal point `c + G β`, and the remainder in the box
  refine ⟨fun r => toReal (S.c r) + ∑ j, toReal (S.G j r) * toRealVec β j,
    SpectraShadow.mem_nominalSet_iff.mpr ⟨toRealVec β, hPSD, fun _ => rfl⟩,
    fun r => toReal (p r) - (toReal (S.c r) + ∑ j, toReal (S.G j r) * toRealVec β j),
    fun r => ?_, ?_⟩
  · -- the remainder lies between the two roundings the test compared with the box
    obtain ⟨l₁, l₂⟩ := hbox r
    have d₁ := le_dotUp (fun j => S.G j r) β
    have d₂ := dotDown_le (fun j => S.G j r) β
    have a₁ := add_le_addUp (S.c r) (dotUp (fun j => S.G j r) β)
    have a₂ := addDown_le_add (S.c r) (dotDown (fun j => S.G j r) β)
    have s₁ := subDown_le_sub (p r) (addUp (S.c r) (dotUp (fun j => S.G j r) β))
    have s₂ := sub_le_subUp (p r) (addDown (S.c r) (dotDown (fun j => S.G j r) β))
    have b₁ := toReal_le_of_le l₁
    have b₂ := toReal_le_of_le l₂
    show toReal (S.E.inf r)
        ≤ toReal (p r) - (toReal (S.c r) + ∑ j, toReal (S.G j r) * toReal (β j))
      ∧ toReal (p r) - (toReal (S.c r) + ∑ j, toReal (S.G j r) * toReal (β j))
        ≤ toReal (S.E.sup r)
    constructor <;> linarith
  · -- the point is the nominal point plus the remainder
    funext r
    simp only [Pi.add_apply, toRealVec]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
