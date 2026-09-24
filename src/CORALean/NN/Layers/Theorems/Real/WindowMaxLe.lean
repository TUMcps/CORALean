import CORALean.NN.Layers.Definitions.WindowMax

/-!
# A window's maximum is at most any common bound

The other half of the supremum's characterisation, `Finset.sup'_le`: a bound on every
coordinate bounds the maximum.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem windowMax_le {k : ℕ} {f : Fin (k + 1) → ℝ} {c : ℝ} (h : ∀ l, f l ≤ c) :
    windowMax f ≤ c :=
  Finset.sup'_le _ f fun l _ => h l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
