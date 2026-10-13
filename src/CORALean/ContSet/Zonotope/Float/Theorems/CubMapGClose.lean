module

public import CORALean.ContSet.Zonotope.Float.Operations.CubMapDep
public import CORALean.ContSet.Zonotope.Float.Theorems.CubFoldBracket
public import CORALean.ContSet.Zonotope.Real.Operations.CubMap

@[expose] public section

/-!
# A stored `cubMap` generator is within its gap of the exact one

Generator `l` of the stored zonotope, rounded down, is off the exact generator of
`Real.Zonotope.cubMap` on the read-back operand by at most `cubMapGDiff`: the exact one is between
the two roundings (`cubFold_bracket`, halved at the pure squares, zero off the sorted triples).
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

theorem Zonotope.cubMapG_close (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) (i : Fin m)
    (l : Fin ((Z.h + 1) * (Z.h + 1) * (Z.h + 1))) :
    |(Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n))).G l i
        - toReal (Zonotope.cubMapGDown T Z i l)|
      ≤ toReal (Zonotope.cubMapGDiff T Z i l) := by -- --- PROOF ---
  have hgap := sub_le_subUp (Zonotope.cubMapGUp T Z i l) (Zonotope.cubMapGDown T Z i l)
  have hb := Zonotope.cubFold_bracket T Z i
  simp only [Zonotope.cubMapGDiff]
  simp only [Zonotope.cubMapGDown, Zonotope.cubMapGUp] at hgap ⊢
  show |(let t := Real.Zonotope.cubIdx (Z.h + 1) (Z.h + 1) (Z.h + 1) l
      if t.1.1 ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧ ¬(t.1.1 = 0 ∧ t.1.2 = 0 ∧ t.2 = 0) then
        (if t.1.1 = 0 ∧ t.1.2 = t.2 then 1 / 2 else 1)
          * Real.Zonotope.cubFold (fun i k => toRealMat (T i k))
            (nominal Z : Real.Zonotope (Vec ℝ n)) i t.1.1 t.1.2 t.2
      else 0) - _| ≤ _
  -- the triple of the generator
  generalize Real.Zonotope.cubIdx (Z.h + 1) (Z.h + 1) (Z.h + 1) l = t at hgap ⊢
  obtain ⟨⟨a, b⟩, c⟩ := t
  have hab := hb a b c
  -- on the sorted triples (halved at the pure squares) and off them
  by_cases hc : a ≤ b ∧ b ≤ c ∧ ¬(a = 0 ∧ b = 0 ∧ c = 0)
  · by_cases hh : a = 0 ∧ b = c
    · simp only [if_pos hc, if_pos hh, toReal_half] at hgap ⊢
      rw [abs_le]
      constructor <;> linarith [hab.1, hab.2]
    · simp only [if_pos hc, if_neg hh] at hgap ⊢
      rw [abs_le]
      constructor <;> linarith [hab.1, hab.2]
  · simp only [if_neg hc, toReal_zero, sub_zero] at hgap ⊢
    simp only [abs_zero]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
