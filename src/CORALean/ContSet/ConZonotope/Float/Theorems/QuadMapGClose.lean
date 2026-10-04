import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDiff
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadBilBracket
import CORALean.ContSet.ConZonotope.Real.Operations.QuadMap

/-!
# A stored generator of `quadMap` is within its gap of the exact one

Entry by entry, the exact generator of [1, Lemma 1] on the read-back operand lies between the two
directed roundings: the linear and the pair generators are sums of two bilinear forms, so their
bounds add, the square's is half of one, halving being exact, and a pair off `j < k` is `0` on both
sides. The stored one is the lower, so its error is at most the gap `quadMapGDiff` records.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact layer's generators on the read-back operand, at this layer's index type. -/
noncomputable def ConZonotope.aux_quadMapGReal (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 n) :
    Fin m → Fin (cZ.h + cZ.h + cZ.h * cZ.h) → ℝ :=
  fun i l => Fin.append
    (Fin.append
      (fun j i => toRealVec cZ.c ⬝ᵥ (toRealMat (Q i) *ᵥ toRealVec fun r => cZ.G r j)
        + (toRealVec fun r => cZ.G r j) ⬝ᵥ (toRealMat (Q i) *ᵥ toRealVec cZ.c))
      (fun j i => (1 / 2) * (toRealVec fun r => cZ.G r j) ⬝ᵥ
        (toRealMat (Q i) *ᵥ toRealVec fun r => cZ.G r j)))
    (fun l i =>
      if (finProdFinEquiv.symm l).1 < (finProdFinEquiv.symm l).2
      then (toRealVec fun r => cZ.G r (finProdFinEquiv.symm l).1) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec fun r => cZ.G r (finProdFinEquiv.symm l).2)
        + (toRealVec fun r => cZ.G r (finProdFinEquiv.symm l).2) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec fun r => cZ.G r (finProdFinEquiv.symm l).1)
      else 0) l i

/-- The exact generator lies between the two stored roundings. -/
theorem ConZonotope.aux_quadMapG_between (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 n)
    (i : Fin m) (l : Fin (cZ.h + cZ.h + cZ.h * cZ.h)) :
    toReal (ConZonotope.quadMapGDown Q cZ i l) ≤ ConZonotope.aux_quadMapGReal Q cZ i l
      ∧ ConZonotope.aux_quadMapGReal Q cZ i l
        ≤ toReal (ConZonotope.quadMapGUp Q cZ i l) := by -- --- PROOF ---
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    · -- the linear generator, two bilinear forms added
      obtain ⟨a1, a2⟩ := ConZonotope.quadBil_bracket (Q i) cZ.c fun r => cZ.G r j
      obtain ⟨b1, b2⟩ := ConZonotope.quadBil_bracket (Q i) (fun r => cZ.G r j) cZ.c
      have h1 := addDown_le_add (ConZonotope.quadBilDown (Q i) cZ.c fun r => cZ.G r j)
        (ConZonotope.quadBilDown (Q i) (fun r => cZ.G r j) cZ.c)
      have h2 := add_le_addUp (ConZonotope.quadBilUp (Q i) cZ.c fun r => cZ.G r j)
        (ConZonotope.quadBilUp (Q i) (fun r => cZ.G r j) cZ.c)
      simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_left]
      exact ⟨by linarith, by linarith⟩
    · -- the square, half of one bilinear form
      obtain ⟨a1, a2⟩ := ConZonotope.quadBil_bracket (Q i) (fun r => cZ.G r j)
        fun r => cZ.G r j
      simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_left, Fin.append_right, toReal_half]
      exact ⟨by linarith, by linarith⟩
  · -- the pairs, a sum off the diagonal and zero on it
    by_cases hjk : (finProdFinEquiv.symm l).1 < (finProdFinEquiv.symm l).2
    · obtain ⟨a1, a2⟩ := ConZonotope.quadBil_bracket (Q i)
        (fun r => cZ.G r (finProdFinEquiv.symm l).1) fun r => cZ.G r (finProdFinEquiv.symm l).2
      -- both orders of the pair, each bracketed
      obtain ⟨b1, b2⟩ := ConZonotope.quadBil_bracket (Q i)
        (fun r => cZ.G r (finProdFinEquiv.symm l).2) fun r => cZ.G r (finProdFinEquiv.symm l).1
      have h1 := addDown_le_add
        (ConZonotope.quadBilDown (Q i) (fun r => cZ.G r (finProdFinEquiv.symm l).1)
          fun r => cZ.G r (finProdFinEquiv.symm l).2)
        (ConZonotope.quadBilDown (Q i) (fun r => cZ.G r (finProdFinEquiv.symm l).2)
          fun r => cZ.G r (finProdFinEquiv.symm l).1)
      have h2 := add_le_addUp
        (ConZonotope.quadBilUp (Q i) (fun r => cZ.G r (finProdFinEquiv.symm l).1)
          fun r => cZ.G r (finProdFinEquiv.symm l).2)
        (ConZonotope.quadBilUp (Q i) (fun r => cZ.G r (finProdFinEquiv.symm l).2)
          fun r => cZ.G r (finProdFinEquiv.symm l).1)
      simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_right, if_pos hjk]
      exact ⟨by linarith, by linarith⟩
    · simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_right, if_neg hjk, toReal_zero]
      exact ⟨le_refl _, le_refl _⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.quadMapG_close (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 n) (i : Fin m)
    (l : Fin (cZ.h + cZ.h + cZ.h * cZ.h)) :
    |(Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i
        - toReal (ConZonotope.quadMapGDown Q cZ i l)|
      ≤ toReal (ConZonotope.quadMapGDiff Q cZ i l) := by -- --- PROOF ---
  -- the exact layer's generator is the table at this layer's index type
  have hreal : (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i
      = ConZonotope.aux_quadMapGReal Q cZ i l := rfl
  rw [hreal]
  obtain ⟨h1, h2⟩ := ConZonotope.aux_quadMapG_between Q cZ i l
  have h3 := sub_le_subUp (ConZonotope.quadMapGUp Q cZ i l) (ConZonotope.quadMapGDown Q cZ i l)
  rw [abs_le]
  simp only [ConZonotope.quadMapGDiff]
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
