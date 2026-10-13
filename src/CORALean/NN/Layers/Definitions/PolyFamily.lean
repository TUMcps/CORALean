module

public import CORALean.NN.Layers.Theorems.Real.ExistsPolyRelaxationErrorLt

@[expose] public section

/-!
# The polynomial relaxation family a refinement loop runs

Level `o` fits `σ` on `[-o, o]` to within `1 / (o + 1)`. A polynomial is unbounded, so no
single fit serves every input set, and a level has to say where it is accurate as well as how
accurately. Built by choice, `exists_polyRelaxation_error_lt` being an existence statement:
CORA's `poly_method` is one witness of many, and soundness answers for every one of them. A
specification over ℝ, as the sampling it rests on is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {σ σ' : ℝ → ℝ} {Mσ : ℝ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Level `o` fits `σ` on `[-o, o]` to within `1 / (o + 1)`. -/
noncomputable def polyRelaxationFamily (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hσ : ∀ x, |σ' x| ≤ Mσ) : PolyRelaxationFamily ℝ where
  deg o := (exists_polyRelaxation_error_lt (L := -(o : ℝ)) (U := (o : ℝ)) hd hσ
    (show (0 : ℝ) < 1 / ((o : ℝ) + 1) by positivity)).choose
  rel o := (exists_polyRelaxation_error_lt (L := -(o : ℝ)) (U := (o : ℝ)) hd hσ
    (show (0 : ℝ) < 1 / ((o : ℝ) + 1) by positivity)).choose_spec.choose

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
