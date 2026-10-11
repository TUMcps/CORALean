import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Theorems.FaceCentrallySymmetric

/-!
# [1, Prop. 1]: zonotopes are not closed under Minkowski difference

[1]'s own counterexample, `Z_m = (0, G⁽ᵐ⁾)` and `Z_s = (0, G⁽ˢ⁾)` with

    G⁽ᵐ⁾ = [[1,1,0,0],[1,0,1,0],[1,0,0,1]],  G⁽ˢ⁾ = G⁽ᵐ⁾/3 with the first
                                              column's first entry negated.

[1] proves it by plotting the difference in Fig. 6 and observing that a face of
it is not centrally symmetric. That face is named here: the difference is
bounded by `x₂ ≤ 4/3`, `x₂ - x₁ ≤ 2/3`, `x₁ - x₃ ≤ 2/3` and `x₃ ≤ 4/3`, and
`(2/3, 4/3, 0)`, `(2/3, 4/3, 4/3)` and `(4/3, 4/3, 4/3)` all lie on `x₂ = 4/3`.
Reflecting those three in any centre drives one of them out, so the face is not
symmetric — and `face_centrally_symmetric` says a zonotope has no such face.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

-- three explicit memberships and four explicit halfspaces, all in coordinates
set_option maxHeartbeats 100000 in
/-- [1, Prop. 1]: at the paper's own three-dimensional pair, the Minkowski
difference of two zonotopes is not a zonotope. -/
theorem Zonotope.minkowskiDiff_not_zonotope :
    ∃ Zm Zs : Zonotope (Vec ℝ 3),
      ¬ ∃ Z : Zonotope (Vec ℝ 3),
        minkowskiDiff Zm.construct Zs.construct = Z.construct := by -- --- PROOF ---
  classical
  set Gm : Fin 4 → Vec ℝ 3 := ![![1, 1, 1], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] with hGm
  set Gs : Fin 4 → Vec ℝ 3 :=
    ![![-(1/3), 1/3, 1/3], ![1/3, 0, 0], ![0, 1/3, 0], ![0, 0, 1/3]] with hGs
  refine ⟨⟨4, 0, Gm⟩, ⟨4, 0, Gs⟩, ?_⟩
  -- a point of the minuend, read off its three coordinates
  have hmemM : ∀ (y : Vec ℝ 3) (b0 b1 b2 b3 : ℝ), |b0| ≤ 1 → |b1| ≤ 1 → |b2| ≤ 1 →
      |b3| ≤ 1 → y 0 = b0 + b1 → y 1 = b0 + b2 → y 2 = b0 + b3 →
      y ∈ Zonotope.construct ⟨4, 0, Gm⟩ := by
    intro y b0 b1 b2 b3 h0 h1 h2 h3 e0 e1 e2
    refine ⟨![b0, b1, b2, b3], ?_, ?_⟩
    · intro j
      fin_cases j
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3
    · funext i
      fin_cases i <;> simp [hGm, Fin.sum_univ_four, e0, e1, e2]
  -- and of the subtrahend, at the coefficients `mu`
  have hmemS : ∀ mu : Fin 4 → ℝ, (∀ j, |mu j| ≤ 1) →
      (![(-mu 0 + mu 1) / 3, (mu 0 + mu 2) / 3, (mu 0 + mu 3) / 3] : Vec ℝ 3)
        ∈ Zonotope.construct ⟨4, 0, Gs⟩ := by
    intro mu hmu
    refine ⟨mu, hmu, ?_⟩
    funext i
    fin_cases i <;> simp [hGs, Fin.sum_univ_four] <;> ring
  -- and the same reading of a point of the subtrahend, run backwards
  have hdestS : ∀ z ∈ Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3)),
      ∃ mu : Fin 4 → ℝ, (∀ j, |mu j| ≤ 1) ∧ z 0 = (-mu 0 + mu 1) / 3 ∧
        z 1 = (mu 0 + mu 2) / 3 ∧ z 2 = (mu 0 + mu 3) / 3 := by
    intro z hz
    obtain ⟨mu, hmu, heq⟩ := hz
    refine ⟨mu, hmu, ?_, ?_, ?_⟩
    · have h := congrFun heq 0
      simp [hGs, Fin.sum_univ_four] at h
      linarith only [h]
    · have h := congrFun heq 1
      simp [hGs, Fin.sum_univ_four] at h
      linarith only [h]
    · have h := congrFun heq 2
      simp [hGs, Fin.sum_univ_four] at h
      linarith only [h]
  -- what a point of the difference must satisfy, once `mu` is chosen
  have hread : ∀ x ∈ minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))),
      ∀ mu : Fin 4 → ℝ, (∀ j, |mu j| ≤ 1) →
      ∃ b : Fin 4 → ℝ, (∀ j, |b j| ≤ 1) ∧
        x 0 + (-mu 0 + mu 1) / 3 = b 0 + b 1 ∧
        x 1 + (mu 0 + mu 2) / 3 = b 0 + b 2 ∧
        x 2 + (mu 0 + mu 3) / 3 = b 0 + b 3 := by
    intro x hx mu hmu
    -- the chosen subtrahend point lands in the minuend, bounding each coordinate
    obtain ⟨b, hb, heq⟩ := hx _ (hmemS mu hmu)
    refine ⟨b, hb, ?_, ?_, ?_⟩
    · have h := congrFun heq 0
      simp [hGm, Fin.sum_univ_four] at h
      linarith only [h]
    · have h := congrFun heq 1
      simp [hGm, Fin.sum_univ_four] at h
      linarith only [h]
    · have h := congrFun heq 2
      simp [hGm, Fin.sum_univ_four] at h
      linarith only [h]
  -- `x₂ - x₁ ≤ 2/3`, the first of the four rows of [1, Thm. 2] the argument needs
  have hC2 : ∀ x ∈ minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))), x 1 - x 0 ≤ 2 / 3 := by
    intro x hx
    obtain ⟨b, hb, e0, e1, -⟩ := hread x hx ![1, -1, 1, 0] (by intro j; fin_cases j <;> norm_num)
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at e0 e1
    linarith only [e0, e1, (abs_le.mp (hb 1)).1, (abs_le.mp (hb 2)).2]
  -- `x₂ ≤ 4/3`, the row the face is cut out by
  have hC3 : ∀ x ∈ minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))), x 1 ≤ 4 / 3 := by
    intro x hx
    obtain ⟨b, hb, -, e1, -⟩ := hread x hx ![1, 0, 1, 0] (by intro j; fin_cases j <;> norm_num)
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at e1
    linarith only [e1, (abs_le.mp (hb 0)).2, (abs_le.mp (hb 2)).2]
  -- `x₁ - x₃ ≤ 2/3`, the row that tilts the face
  have hC4 : ∀ x ∈ minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))), x 0 - x 2 ≤ 2 / 3 := by
    intro x hx
    obtain ⟨b, hb, e0, -, e2⟩ := hread x hx ![-1, 1, 0, -1] (by intro j; fin_cases j <;> norm_num)
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at e0 e2
    linarith only [e0, e2, (abs_le.mp (hb 1)).2, (abs_le.mp (hb 3)).1]
  -- `x₃ ≤ 4/3`, the last of the four
  have hC5 : ∀ x ∈ minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))), x 2 ≤ 4 / 3 := by
    intro x hx
    obtain ⟨b, hb, -, -, e2⟩ := hread x hx ![1, 0, 0, 1] (by intro j; fin_cases j <;> norm_num)
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at e2
    linarith only [e2, (abs_le.mp (hb 0)).2, (abs_le.mp (hb 3)).2]
  -- three points of the face `x₂ = 4/3`
  have hA : (![2 / 3, 4 / 3, 0] : Vec ℝ 3) ∈
      minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))) := by
    intro z hz
    obtain ⟨mu, hmu, e0, e1, e2⟩ := hdestS z hz
    have m0 := abs_le.mp (hmu 0)
    have m1 := abs_le.mp (hmu 1)
    have m2 := abs_le.mp (hmu 2)
    have m3 := abs_le.mp (hmu 3)
    refine hmemM _ ((mu 0 + 2) / 3) ((mu 1 - 2 * mu 0) / 3) ((2 + mu 2) / 3)
      ((mu 3 - 2) / 3) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    -- and the three coordinates match the minuend's coefficients
    · show (2:ℝ) / 3 + z 0 = _
      rw [e0]; ring
    · show (4:ℝ) / 3 + z 1 = _
      rw [e1]; ring
    · show (0:ℝ) + z 2 = _
      rw [e2]; ring
  -- the second of the three, one edge along from the first
  have hB : (![2 / 3, 4 / 3, 4 / 3] : Vec ℝ 3) ∈
      minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))) := by
    intro z hz
    obtain ⟨mu, hmu, e0, e1, e2⟩ := hdestS z hz
    have m0 := abs_le.mp (hmu 0)
    have m1 := abs_le.mp (hmu 1)
    have m2 := abs_le.mp (hmu 2)
    have m3 := abs_le.mp (hmu 3)
    refine hmemM _ ((mu 0 + 2) / 3) ((mu 1 - 2 * mu 0) / 3) ((2 + mu 2) / 3)
      ((2 + mu 3) / 3) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    -- and the three coordinates match the minuend's coefficients
    · show (2:ℝ) / 3 + z 0 = _
      rw [e0]; ring
    · show (4:ℝ) / 3 + z 1 = _
      rw [e1]; ring
    · show (4:ℝ) / 3 + z 2 = _
      rw [e2]; ring
  -- and the corner of the face
  have hD : (![4 / 3, 4 / 3, 4 / 3] : Vec ℝ 3) ∈
      minkowskiDiff (Zonotope.construct (⟨4, 0, Gm⟩ : Zonotope (Vec ℝ 3)))
        (Zonotope.construct (⟨4, 0, Gs⟩ : Zonotope (Vec ℝ 3))) := by
    intro z hz
    obtain ⟨mu, hmu, e0, e1, e2⟩ := hdestS z hz
    have m0 := abs_le.mp (hmu 0)
    have m1 := abs_le.mp (hmu 1)
    have m2 := abs_le.mp (hmu 2)
    have m3 := abs_le.mp (hmu 3)
    refine hmemM _ 1 ((1 - mu 0 + mu 1) / 3) ((1 + mu 0 + mu 2) / 3)
      ((1 + mu 0 + mu 3) / 3) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    · rw [abs_le]; constructor <;>
      linarith only [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2]
    -- and the three coordinates match the minuend's coefficients
    · show (4:ℝ) / 3 + z 0 = _
      rw [e0]; ring
    · show (4:ℝ) / 3 + z 1 = _
      rw [e1]; ring
    · show (4:ℝ) / 3 + z 2 = _
      rw [e2]; ring
  -- were the difference a zonotope, that face would be symmetric about a point
  rintro ⟨Z, hZ⟩
  have hbnd : ∀ x ∈ Z.construct, (LinearMap.proj 1 : Vec ℝ 3 →ₗ[ℝ] ℝ) x ≤ 4 / 3 := by
    intro x hx
    rw [← hZ] at hx
    exact hC3 x hx
  obtain ⟨m, hm⟩ := Z.face_centrally_symmetric (LinearMap.proj 1) (4 / 3) hbnd
  obtain ⟨hyA, -⟩ := hm _ (hZ ▸ hA) (by simp)
  obtain ⟨hyB, -⟩ := hm _ (hZ ▸ hB) (by simp)
  obtain ⟨hyD, hyDu⟩ := hm _ (hZ ▸ hD) (by simp)
  rw [← hZ] at hyA hyB hyD
  -- and the three reflected points leave the difference
  have c5 := hC5 _ hyA
  have c4 := hC4 _ hyB
  have c2 := hC2 _ hyD
  simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at c5 c4 c2 hyDu
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
