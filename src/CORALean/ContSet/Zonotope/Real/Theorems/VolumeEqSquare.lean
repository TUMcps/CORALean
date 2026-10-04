import CORALean.ContSet.Zonotope.Real.Operations.Volume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The volume of a zonotope with `n` generators

The zonotope is `c` plus the image of the cube `[-1, 1]^n` under the matrix of its generators,
so its volume is `|det G|` times the cube's, `2^n` (`Measure.addHaar_image_linearMap`). With
exactly `n` generators the one `n`-subset is all of them. This is `Zonotope.volume` in the case
`h = n`: the general sum (the tiling by parallelotopes) is not proved.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.volume_eq_of_h_eq (Z : Zonotope (Vec ℝ n)) (hh : Z.h = n) :
    MeasureTheory.volume Z.construct = Z.volume := by -- --- PROOF ---
  obtain ⟨h, c, G⟩ := Z
  simp only at hh
  subst hh
  -- the generator matrix `M` has the generators as columns
  let M : Mat ℝ h h := Matrix.of fun i k => G k i
  -- the zonotope is a translate of the image of the cube
  have hcon : (Zonotope.mk h c G).construct =
      (fun v => -c + v) ⁻¹' ((Matrix.toLin' M) '' Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1)) := by
    ext x
    simp only [Zonotope.construct, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image,
      Set.mem_Icc]
    constructor
    · -- a point of the zonotope
      rintro ⟨β, hβ, rfl⟩
      refine ⟨β, ⟨fun j => (abs_le.mp (hβ j)).1, fun j => (abs_le.mp (hβ j)).2⟩, ?_⟩
      ext i
      simp [M, Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply]
    · -- a point of the translated image
      rintro ⟨β, ⟨h1, h2⟩, hx⟩
      refine ⟨β, fun j => abs_le.mpr ⟨h1 j, h2 j⟩, ?_⟩
      have : x = c + Matrix.toLin' M β := by rw [hx]; abel
      rw [this]
      congr 1
      ext i
      simp [M, Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply]
  -- translation keeps the volume; the image scales the cube's by `|det M|`
  rw [hcon, measure_preimage_add, Measure.addHaar_image_linearMap, Real.volume_Icc_pi,
    LinearMap.det_toLin']
  simp only [sub_neg_eq_add, one_add_one_eq_two, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  -- only the full index set has `h` elements
  unfold Zonotope.volume
  -- the sum has one nonzero term, the full index set, whose order embedding is the identity
  have hsum : ∑ S : Finset (Fin h),
      (if hS : S.card = h then
        |(Matrix.of fun i k => G (S.orderEmbOfFin hS k) i : Mat ℝ h h).det| else 0) = |M.det| := by
    rw [Finset.sum_eq_single (Finset.univ : Finset (Fin h))]
    · rw [dif_pos (Finset.card_univ.trans (Fintype.card_fin h))]
      congr 2
      have hid : ∀ k, (Finset.univ : Finset (Fin h)).orderEmbOfFin
          (Finset.card_univ.trans (Fintype.card_fin h)) k = k := fun k => by
        rw [← Finset.orderEmbOfFin_unique' (Finset.card_univ.trans (Fintype.card_fin h))
          (f := (OrderIso.refl (Fin h)).toOrderEmbedding) (fun _ => Finset.mem_univ _)]
        rfl
      simp only [hid]
      rfl
    · -- any other index set has fewer than `h` elements
      intro S _ hS
      rw [dif_neg]
      intro hcard
      exact hS (Finset.eq_univ_of_card S (hcard.trans (Fintype.card_fin h).symm))
    · simp
  rw [hsum, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp [mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
