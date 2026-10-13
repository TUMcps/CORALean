import CORALean.Global.Float.SoundFloatArithmetic

/-!
# Directed sums of a list

`sumUp` and `sumDown` over a `List` rather than a `Fin n`-indexed family: a Taylor model's
terms are a list whose length an operation does not know in advance. Right-nested, as
`sumUp` is, so each bound is one induction.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def listSumUp : List 𝕋 → 𝕋
  | [] => zero
  | a :: l => addUp a (listSumUp l)

def listSumDown : List 𝕋 → 𝕋
  | [] => zero
  | a :: l => addDown a (listSumDown l)

theorem sum_le_listSumUp [SoundFloatArithmetic 𝕋] (l : List 𝕋) :
    (l.map toReal).sum ≤ toReal (listSumUp l) := by -- --- PROOF ---
  induction l with
  | nil => simp [listSumUp, toReal_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, listSumUp]
    exact le_trans (by linarith) (add_le_addUp _ _)

theorem listSumDown_le [SoundFloatArithmetic 𝕋] (l : List 𝕋) :
    toReal (listSumDown l) ≤ (l.map toReal).sum := by -- --- PROOF ---
  induction l with
  | nil => simp [listSumDown, toReal_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, listSumDown]
    exact le_trans (addDown_le_add _ _) (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
