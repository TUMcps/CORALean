import CORALean.NN.Layers.Definitions.WindowMax

/-!
# Every coordinate of a window is at most its maximum

The supremum bounds each of its arguments; `Finset.le_sup'` at the window's own index.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_windowMax {k : ℕ} (f : Fin (k + 1) → ℝ) (l : Fin (k + 1)) : f l ≤ windowMax f :=
  Finset.le_sup' f (Finset.mem_univ l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
