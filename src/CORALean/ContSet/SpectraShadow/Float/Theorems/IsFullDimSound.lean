module

public import CORALean.ContSet.SpectraShadow.Float.Operations.IsFullDim
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PosSemidefOfDiagDominant
public import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# A `true` from `SpectraShadow.isFullDim` proves an interior point

Every coefficient vector within `δ` of `β` makes the combination symmetric, with each entry
between the two roundings the test compared and the diagonal dominating its row, so positive
semidefinite (`SpectraShadow.posSemidef_of_diagDominant`): the open box of coefficients lies in
the spectrahedron. The generators reach a ball, so `β ↦ c + G β` is onto and open
(`LinearMap.isOpenMap_of_finiteDimensional`), and the image of the box is an open set of the
nominal shadow; the error box, ordered, moves it into the shadow.

## Inputs
* `S` – spectrahedral shadow
* `β` – center of the coefficient box
* `δ` – radius of the coefficient box

## Hypotheses
* `h` – `S.isFullDim β δ` holds

## Conclusion
* the shadow has an interior point
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Generators that reach a ball around the origin map onto the whole space. -/
private theorem aux_surjective (S : SpectraShadow 𝕋 (Vec 𝕋 n)) {H : Mat 𝕋 S.m n} {B : 𝕋}
    (hc : Zonotope.ballCert (fun i j => S.G j i) H B one = true) : -- --- CONCL ---
    Function.Surjective (Matrix.mulVecLin (toRealMat fun i j => S.G j i)) := by -- --- PROOF ---
  obtain ⟨hB, hreach⟩ := Zonotope.ballCert_reach hc
  intro y
  -- scale `y` into the ball, solve, and scale the coefficients back
  set N : ℝ := (∑ i, |y i|) / toReal B + 1 with hN
  have hNpos : 0 < N := by positivity
  obtain ⟨γ, hγ, -⟩ := hreach (fun i => y i / N) fun i => by
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    have := Finset.single_le_sum (f := fun i => |y i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h2 : (∑ i, |y i|) = (N - 1) * toReal B := by
      rw [hN]; field_simp; ring
    nlinarith
  refine ⟨N • γ, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hγ]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- A symmetric matrix between two roundings, whose lower diagonal dominates the larger of the
magnitudes of the bounds in its row, is positive semidefinite. -/
private theorem aux_psd {k : ℕ} (M : Mat ℝ k k) (lo hi : Mat 𝕋 k k)
    (hsym : ∀ i j, M j i = M i j) (hlo : ∀ i j, toReal (lo i j) ≤ M i j)
    (hhi : ∀ i j, M i j ≤ toReal (hi i j))
    (hdom : ∀ i, le (sumUp fun j => if j = i then zero else maximum (hi i j) (neg (lo i j)))
      (lo i i) = true) : -- --- CONCL ---
    M.PosSemidef := by -- --- PROOF ---
  -- diagonal dominance of the matrix, from that of the bounds
  refine SpectraShadow.posSemidef_of_diagDominant M hsym fun i => ?_
  refine le_trans ?_ (le_trans (toReal_le_of_le (hdom i)) (hlo i i))
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
  by_cases hj : j = i
  · simp [hj, toReal_zero]
  · simp only [hj, if_false, toReal_maximum, toReal_neg]
    have m₁ := le_max_left (toReal (hi i j)) (-toReal (lo i j))
    have m₂ := le_max_right (toReal (hi i j)) (-toReal (lo i j))
    have l₁ := hlo i j
    have h₁ := hhi i j
    exact abs_le'.mpr ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.isFullDim_sound {S : SpectraShadow 𝕋 (Vec 𝕋 n)} {β : Vec 𝕋 S.m} {δ : 𝕋}
    (h : S.isFullDim β δ = true) : -- --- CONCL ---
    (interior S.construct).Nonempty := by -- --- PROOF ---
  simp only [SpectraShadow.isFullDim, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨⟨hsym, hdom⟩, hδ⟩, hc⟩, hbox⟩ := h
  have hδpos : 0 < toReal δ := by simpa [toReal_zero] using toReal_lt_of_ltStrict hδ
  -- the open box of coefficients around `β`
  set Bset : Set (Vec ℝ S.m) :=
    Set.pi Set.univ fun l => Metric.ball (toReal (β l)) (toReal δ) with hBset
  have hBopen : IsOpen Bset := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  -- at every coefficient vector of the box the matrix is positive semidefinite
  have hPSD : ∀ γ ∈ Bset,
      (toRealMat S.A₀ + ∑ l, γ l • toRealMat (S.A l)).PosSemidef := by
    intro γ hγ
    have hd : ∀ l, |γ l - toReal (β l)| ≤ toReal δ := fun l => by
      have := hγ l (Set.mem_univ l)
      rw [Metric.mem_ball, Real.dist_eq] at this
      exact this.le
    have hent : ∀ i j, (toRealMat S.A₀ + ∑ l, γ l • toRealMat (S.A l)) i j
        = toReal (S.A₀ i j) + ∑ l, γ l * toReal (S.A l i j) := fun i j => by
      simp [Matrix.add_apply, Matrix.sum_apply, toRealMat]
    -- the box moves an entry by at most the rounded-up spread
    have hdev : ∀ i j, |∑ l, γ l * toReal (S.A l i j) - ∑ l, toReal (β l) * toReal (S.A l i j)|
        ≤ toReal (mulUp δ (sumUp fun l => absolute (S.A l i j))) := fun i j => by
      rw [← Finset.sum_sub_distrib]
      calc |∑ l, (γ l * toReal (S.A l i j) - toReal (β l) * toReal (S.A l i j))|
          ≤ ∑ l, |γ l * toReal (S.A l i j) - toReal (β l) * toReal (S.A l i j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, toReal δ * |toReal (S.A l i j)| := Finset.sum_le_sum fun l _ => by
            rw [← sub_mul, abs_mul]
            exact mul_le_mul_of_nonneg_right (hd l) (abs_nonneg _)
        _ = toReal δ * ∑ l, |toReal (S.A l i j)| := (Finset.mul_sum _ _ _).symm
        _ ≤ toReal δ * toReal (sumUp fun l => absolute (S.A l i j)) :=
            mul_le_mul_of_nonneg_left (le_trans (le_of_eq (Finset.sum_congr rfl fun l _ =>
              (toReal_absolute _).symm)) (sum_le_sumUp _)) hδpos.le
        _ ≤ _ := mul_le_mulUp _ _
    -- the rounded bounds of the combination are diagonally dominant, so it is semidefinite
    refine aux_psd _ (fun i j => subDown (addDown (S.A₀ i j) (dotDown β fun l => S.A l i j))
        (mulUp δ (sumUp fun l => absolute (S.A l i j))))
      (fun i j => addUp (addUp (S.A₀ i j) (dotUp β fun l => S.A l i j))
        (mulUp δ (sumUp fun l => absolute (S.A l i j)))) ?_ ?_ ?_ hdom
    · -- the stored matrices are symmetric, so the combination is
      intro i j
      rw [hent, hent]
      have e₀ : toReal (S.A₀ j i) = toReal (S.A₀ i j) :=
        le_antisymm (toReal_le_of_le (hsym j i).1) (toReal_le_of_le (hsym i j).1)
      have eₗ : ∀ l, toReal (S.A l j i) = toReal (S.A l i j) := fun l =>
        le_antisymm (toReal_le_of_le ((hsym j i).2 l)) (toReal_le_of_le ((hsym i j).2 l))
      simp only [e₀, eₗ]
    · -- the lower rounding is below the entry
      intro i j
      rw [hent]
      have h1 := subDown_le_sub (addDown (S.A₀ i j) (dotDown β fun l => S.A l i j))
        (mulUp δ (sumUp fun l => absolute (S.A l i j)))
      have h2 := addDown_le_add (S.A₀ i j) (dotDown β fun l => S.A l i j)
      have h3 := dotDown_le β fun l => S.A l i j
      have h4 := (abs_le.mp (hdev i j)).1
      linarith
    · intro i j
      rw [hent]
      have h2 := add_le_addUp (S.A₀ i j) (dotUp β fun l => S.A l i j)
      have h3 := le_dotUp β fun l => S.A l i j
      have h4 := (abs_le.mp (hdev i j)).2
      have h5 := add_le_addUp (addUp (S.A₀ i j) (dotUp β fun l => S.A l i j))
        (mulUp δ (sumUp fun l => absolute (S.A l i j)))
      linarith
  -- the image of the box under `β ↦ c + G β` is open, as the generators are onto
  have hLopen := LinearMap.isOpenMap_of_finiteDimensional
    (Matrix.mulVecLin (toRealMat fun i j => S.G j i)) (aux_surjective S hc)
  have hWopen : IsOpen ((fun x => toRealVec S.c + x) ''
      (Matrix.mulVecLin (toRealMat fun i j => S.G j i) '' Bset)) :=
    (Homeomorph.addLeft (toRealVec S.c)).isOpenMap _ (hLopen _ hBopen)
  have hβ : toRealVec β ∈ Bset := fun l _ => by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [toRealVec] using hδpos
  have hWsub : ((fun x => toRealVec S.c + x) ''
      (Matrix.mulVecLin (toRealMat fun i j => S.G j i) '' Bset)) ⊆ nominalSet S := by
    rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    refine SpectraShadow.mem_nominalSet_iff.mpr ⟨γ, hPSD γ hγ, fun i => ?_⟩
    simp [Matrix.mulVec, dotProduct, toRealMat, toRealVec]
  have hint := interior_maximal hWsub hWopen (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hβ))
  -- the ordered error box moves an interior point of the nominal shadow into the shadow
  have he : (fun i => toReal (S.I_error.inf i)) ∈ S.I_error.construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hbox i)⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hint he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
