module

public import CORALean.ContSet.Zonotope.Float.Operations.CubFoldDown
public import CORALean.ContSet.Zonotope.Float.Operations.CubFoldUp
public import CORALean.ContSet.Zonotope.Float.Theorems.ListQuadBracket
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.CubFold

@[expose] public section

/-!
# `cubFoldDown` and `cubFoldUp` bracket the coefficients of `Zonotope.cubFold`

The exact coefficient of the sorted triple, on the nominal zonotope the stored floats describe,
lies between the two roundings: `Zonotope.listQuad_bracket` for each `listQuad{j}(a, b)`, and a
directed sum of up to three bracketed terms is bracketed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


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
  have hB := Zonotope.listQuad_bracket T (Fin.cons Z.c Z.G : Fin (Z.h + 1) → Vec 𝕋 n) i
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
