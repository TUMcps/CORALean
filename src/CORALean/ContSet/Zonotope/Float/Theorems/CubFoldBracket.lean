module

public import CORALean.ContSet.Zonotope.Float.Operations.CubFoldDown
public import CORALean.ContSet.Zonotope.Float.Operations.CubFoldUp
public import CORALean.ContSet.Zonotope.Float.Operations.ListQuadUp
public import CORALean.ContSet.Zonotope.Float.Operations.ListQuadDown
public import CORALean.ContSet.Zonotope.Float.Theorems.CubContractBracket
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.CubFold

@[expose] public section

/-!
# `cubFoldDown` and `cubFoldUp` bracket the coefficients of `Zonotope.cubFold`

The exact coefficient of the sorted triple, on the nominal zonotope the stored floats describe,
lies between the two roundings: `Zonotope.aux_listQuad_bracket` for each `listQuad{j}(a, b)`, and a
directed sum of up to three bracketed terms is bracketed.

## Inputs
* `T` – cubic tensor
* `Z` – zonotope
* `i` – output coordinate
* `x` – first column index
* `y` – second column index
* `z` – third column index

## Hypotheses
* none

## Conclusion
* exact coefficient lies between the two roundings
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m N : ℕ}

/-- `listQuadDown` and `listQuadUp` bracket `listQuad`. -/
private theorem Zonotope.aux_listQuad_bracket (T : Fin m → Fin n → Mat 𝕋 n n)
    (Zext : Fin N → Vec 𝕋 n) (i : Fin m) (j a b : Fin N) : -- --- CONCL ---
    let quad : Fin n → ℝ := fun k => if a < b then
        toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext b))
          + toRealVec (Zext b) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
      else if a = b then toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
      else 0
    toReal (Zonotope.listQuadDown T Zext i j a b) ≤ ∑ k, quad k * toRealVec (Zext j) k
      ∧ ∑ k, quad k * toRealVec (Zext j) k
        ≤ toReal (Zonotope.listQuadUp T Zext i j a b) := by -- --- PROOF ---
  intro quad
  simp only [quad]
  have h1 := Zonotope.cubContract_bracket T (Zext j) (Zext a) (Zext b) i
  have h2 := Zonotope.cubContract_bracket T (Zext j) (Zext b) (Zext a) i
  have h3 := Zonotope.cubContract_bracket T (Zext j) (Zext a) (Zext a) i
  -- above the diagonal: the pair and its transpose
  by_cases hab : a < b
  · have hs : ∑ k, (toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext b))
          + toRealVec (Zext b) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a)))
          * toRealVec (Zext j) k
        = ∑ k, toReal (Zext j k) * (toRealVec (Zext a) ⬝ᵥ
            (toRealMat (T i k) *ᵥ toRealVec (Zext b)))
          + ∑ k, toReal (Zext j k) * (toRealVec (Zext b) ⬝ᵥ
            (toRealMat (T i k) *ᵥ toRealVec (Zext a))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [toRealVec]; ring
    simp only [hab, if_true, Zonotope.listQuadDown, Zonotope.listQuadUp]
    rw [hs]
    exact ⟨le_trans (addDown_le_add _ _) (add_le_add h1.1 h2.1),
      le_trans (add_le_add h1.2 h2.2) (add_le_addUp _ _)⟩
  -- on the diagonal: the square; below it: zero
  · by_cases hEq : a = b
    · subst hEq
      simp only [hab, if_false, if_true, Zonotope.listQuadDown, Zonotope.listQuadUp]
      have hs : ∑ k, toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
            * toRealVec (Zext j) k
          = ∑ k, toReal (Zext j k) * (toRealVec (Zext a) ⬝ᵥ
            (toRealMat (T i k) *ᵥ toRealVec (Zext a))) :=
        Finset.sum_congr rfl fun k _ => by simp only [toRealVec]; ring
      rw [hs]
      exact ⟨h3.1, h3.2⟩
    · simp only [hab, hEq, if_false, Zonotope.listQuadDown, Zonotope.listQuadUp, zero_mul,
        Finset.sum_const_zero, toReal_zero]
      exact ⟨le_rfl, le_rfl⟩

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cubFold_bracket (T : Fin m → Fin n → Mat 𝕋 n n)
    (Z : Zonotope (Vec 𝕋 n)) (i : Fin m)
    (x y z : Fin (Z.h + 1)) : -- --- CONCL ---
    toReal (Zonotope.cubFoldDown T Z i x y z)
        ≤ Real.Zonotope.cubFold (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n)) i x y z
      ∧ Real.Zonotope.cubFold (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n)) i x y z
        ≤ toReal (Zonotope.cubFoldUp T Z i x y z) := by -- --- PROOF ---
  -- the extended columns, read back
  have hext : (Fin.cons (nominal Z : Real.Zonotope (Vec ℝ n)).c
        (nominal Z : Real.Zonotope (Vec ℝ n)).G : Fin (Z.h + 1) → Vec ℝ n)
      = fun j => toRealVec ((Fin.cons Z.c Z.G : Fin (Z.h + 1) → Vec 𝕋 n) j) := by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    simp only [Fin.cons_succ]
    rfl
  -- each `listQuad{j}(a, b)`
  have hB := Zonotope.aux_listQuad_bracket T (Fin.cons Z.c Z.G : Fin (Z.h + 1) → Vec 𝕋 n) i
  simp only [Zonotope.cubFoldDown, Zonotope.cubFoldUp, Real.Zonotope.cubFold, hext]
  -- the accumulation: a directed sum of up to three bracketed terms
  refine ⟨le_trans (addDown_le_add _ _) (add_le_add (le_trans (addDown_le_add _ _)
      (add_le_add (hB _ _ _).1 ?b1)) ?b2),
    le_trans (add_le_add (le_trans (add_le_add (hB _ _ _).2 ?b1') (add_le_addUp _ _)) ?b2')
      (add_le_addUp _ _)⟩
  -- the optional terms, present or `0`
  case b1 =>
    by_cases hc : x < z
    · simpa only [hc, if_true] using (hB z x y).1
    · simp [hc, toReal_zero]
  case b1' =>
    by_cases hc : x < z
    · simpa only [hc, if_true] using (hB z x y).2
    · simp [hc, toReal_zero]
  case b2 =>
    by_cases hc : x < y ∧ y < z
    · simpa only [hc, and_self, if_true] using (hB y x z).1
    · simp [hc, toReal_zero]
  case b2' =>
    by_cases hc : x < y ∧ y < z
    · simpa only [hc, and_self, if_true] using (hB y x z).2
    · simp [hc, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
