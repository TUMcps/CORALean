import CORALean.ContSet.Ellipsoid.Float.Operations.CartProdVec
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

/-!
# `Ellipsoid.cartProdVec` is the product with a point, exactly

The padded centre plus the padded generators at `u` is the original point with the point appended,
as the padding rows are zero; the error box is the original's with a zero-width box on the appended
coordinates, so a point of it is a point of the original's with nothing added there.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.cartProdVec_exact (E : Ellipsoid 𝕋 n) (v : Vec 𝕋 m) :
    (E.cartProdVec v).construct =
      (fun x : Vec ℝ n => (Fin.append x (toRealVec v) : Vec ℝ (n + m))) ''
        E.construct := by -- --- PROOF ---
  -- the stored fields on the two parts of the coordinates
  have hql : ∀ i : Fin n, (E.cartProdVec v).q (Fin.castAdd m i) = E.q i := fun i => by
    simp only [Ellipsoid.cartProdVec, Fin.append_left]
  have hqr : ∀ i : Fin m, (E.cartProdVec v).q (Fin.natAdd n i) = v i := fun i => by
    simp only [Ellipsoid.cartProdVec, Fin.append_right]
  have hGl : ∀ (i : Fin n) (j : Fin E.k), (E.cartProdVec v).G (Fin.castAdd m i) j = E.G i j :=
    fun i j => by simp only [Ellipsoid.cartProdVec, Fin.addCases_left]
  have hGr : ∀ (i : Fin m) (j : Fin E.k), (E.cartProdVec v).G (Fin.natAdd n i) j = zero :=
    fun i j => by simp only [Ellipsoid.cartProdVec, Fin.addCases_right]
  have hil : ∀ i : Fin n, (E.cartProdVec v).err.inf (Fin.castAdd m i) = E.err.inf i := fun i => by
    simp only [Ellipsoid.cartProdVec, Fin.append_left]
  have hsl : ∀ i : Fin n, (E.cartProdVec v).err.sup (Fin.castAdd m i) = E.err.sup i := fun i => by
    simp only [Ellipsoid.cartProdVec, Fin.append_left]
  have hir : ∀ i : Fin m, (E.cartProdVec v).err.inf (Fin.natAdd n i) = zero := fun i => by
    simp only [Ellipsoid.cartProdVec, Fin.append_right]
  have hsr : ∀ i : Fin m, (E.cartProdVec v).err.sup (Fin.natAdd n i) = zero := fun i => by
    simp only [Ellipsoid.cartProdVec, Fin.append_right]
  -- the two directions, a point of the product and a point of the factor
  ext x
  constructor
  · rintro ⟨z, hz, e, he, rfl⟩
    obtain ⟨u, hu, hz⟩ := Ellipsoid.mem_nominalSet_iff.mp hz
    -- the first `n` coordinates are the original's, the rest the point
    have he₁ : ∀ i : Fin n, toReal (E.err.inf i) ≤ e (Fin.castAdd m i)
        ∧ e (Fin.castAdd m i) ≤ toReal (E.err.sup i) := fun i => by
      have h : toReal ((E.cartProdVec v).err.inf (Fin.castAdd m i)) ≤ e (Fin.castAdd m i)
          ∧ e (Fin.castAdd m i) ≤ toReal ((E.cartProdVec v).err.sup (Fin.castAdd m i)) :=
        he (Fin.castAdd m i)
      rw [hil, hsl] at h
      exact h
    have he₂ : ∀ i : Fin m, e (Fin.natAdd n i) = 0 := fun i => by
      have h : toReal ((E.cartProdVec v).err.inf (Fin.natAdd n i)) ≤ e (Fin.natAdd n i)
          ∧ e (Fin.natAdd n i) ≤ toReal ((E.cartProdVec v).err.sup (Fin.natAdd n i)) :=
        he (Fin.natAdd n i)
      rw [hir, hsr, toReal_zero] at h
      exact le_antisymm h.2 h.1
    -- the same for the generator sum, whose appended rows are zero
    have hz₁ : ∀ i : Fin n, z (Fin.castAdd m i)
        = toReal (E.q i) + ∑ j, toReal (E.G i j) * u j := fun i => by
      have h := hz (Fin.castAdd m i)
      simp only [hql, hGl] at h
      exact h
    have hz₂ : ∀ i : Fin m, z (Fin.natAdd n i) = toReal (v i) := fun i => by
      have h := hz (Fin.natAdd n i)
      simp only [hqr, hGr, toReal_zero, zero_mul, Finset.sum_const_zero, add_zero] at h
      exact h
    -- the original's point is the first coordinates, its error those of the box
    refine ⟨fun i => z (Fin.castAdd m i) + e (Fin.castAdd m i),
      ⟨fun i => z (Fin.castAdd m i), Ellipsoid.mem_nominalSet_iff.mpr ⟨u, hu, hz₁⟩,
        fun i => e (Fin.castAdd m i), he₁, rfl⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      rfl
    · simp only [Fin.append_right]
      show toReal (v i) = z (Fin.natAdd n i) + e (Fin.natAdd n i)
      rw [hz₂, he₂, add_zero]
  · -- the other way: a point of the factor, with the point appended and nothing added
    rintro ⟨_, ⟨z, hz, e, he, rfl⟩, rfl⟩
    obtain ⟨u, hu, hz⟩ := Ellipsoid.mem_nominalSet_iff.mp hz
    refine ⟨Fin.append z (toRealVec v), Ellipsoid.mem_nominalSet_iff.mpr ⟨u, hu, fun i => ?_⟩,
      Fin.append e 0, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · show Fin.append z (toRealVec v) (Fin.castAdd m i) = toReal ((E.cartProdVec v).q
          (Fin.castAdd m i)) + ∑ j, toReal ((E.cartProdVec v).G (Fin.castAdd m i) j) * u j
        simp only [hql, hGl, Fin.append_left]
        exact hz i
      · show Fin.append z (toRealVec v) (Fin.natAdd n i) = toReal ((E.cartProdVec v).q
          (Fin.natAdd n i)) + ∑ j, toReal ((E.cartProdVec v).G (Fin.natAdd n i) j) * u j
        simp only [hqr, hGr, toReal_zero, zero_mul, Finset.sum_const_zero, add_zero,
          Fin.append_right]
        rfl
    -- the appended error is zero, the first coordinates' the original's
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · show toReal ((E.cartProdVec v).err.inf (Fin.castAdd m i)) ≤ Fin.append e 0 (Fin.castAdd m i)
          ∧ Fin.append e 0 (Fin.castAdd m i) ≤ toReal ((E.cartProdVec v).err.sup (Fin.castAdd m i))
        rw [hil, hsl, Fin.append_left]
        exact he i
      · show toReal ((E.cartProdVec v).err.inf (Fin.natAdd n i)) ≤ Fin.append e 0 (Fin.natAdd n i)
          ∧ Fin.append e 0 (Fin.natAdd n i) ≤ toReal ((E.cartProdVec v).err.sup (Fin.natAdd n i))
        rw [hir, hsr, Fin.append_right, toReal_zero]
        exact ⟨le_refl _, le_refl _⟩
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Pi.add_apply, Fin.append_left]
      · simp only [Pi.add_apply, Fin.append_right]
        show toReal (v i) + 0 = toReal (v i)
        rw [add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
