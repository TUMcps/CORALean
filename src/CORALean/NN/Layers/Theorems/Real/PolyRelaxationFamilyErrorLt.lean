import CORALean.NN.Layers.Definitions.PolyFamily

/-!
# Each level of the family is accurate on its range

ℝ-only, as the family is: level `o`'s error is under `1 / (o + 1)` on every box in `[-o, o]`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem polyRelaxationFamily_error_lt {σ σ' : ℝ → ℝ} {Mσ : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, |σ' x| ≤ Mσ) (o : ℕ) {l u : ℝ}
    (hl : -(o : ℝ) ≤ l) (hlu : l ≤ u) (hu : u ≤ (o : ℝ)) :
    ((polyRelaxationFamily hd hσ).rel o).error l u < 1 / ((o : ℝ) + 1) :=
  (exists_polyRelaxation_error_lt (L := -(o : ℝ)) (U := (o : ℝ)) hd hσ
    (show (0 : ℝ) < 1 / ((o : ℝ) + 1) by positivity)).choose_spec.choose_spec.2 l u hl hlu hu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
