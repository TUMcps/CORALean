import CORALean.Global.Float.FloatOps
import Mathlib.Order.Fin.Basic

/-!
# `Zonotope.detCandidate`

A determinant in the scalar's own arithmetic, by Laplace expansion along the first row, every
product and the sum rounded down. It is a candidate and nothing more: the rankings it feeds
(`dominantShortlist`, `dominantScore`) and the facet normals `minnorm` forms are heuristics or are
bounded afterwards, so no theorem about the number it returns is needed. The sign `(-1)^j` is the
exact `one` or `neg one`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The determinant of a square matrix by expansion along row zero, rounded down. -/
def Zonotope.detCandidate : {d : ℕ} → Mat 𝕋 d d → 𝕋
  | 0, _ => one
  | _ + 1, A =>
    sumDown fun j =>
      let s : 𝕋 := if (j : ℕ) % 2 = 0 then one else neg one                  -- (-1)^j
      mulDown (mulDown s (A 0 j)) (Zonotope.detCandidate fun i k => A i.succ (j.succAbove k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
