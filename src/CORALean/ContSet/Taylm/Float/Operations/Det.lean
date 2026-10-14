module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.Smul
public import CORALean.ContSet.Taylm.Float.Operations.Times

@[expose] public section

/-!
# `Taylm.det`, over a floating-point scalar

Expansion along the first row, as in the exact layer. The sign `(-1)^j` is the exact float `one`
or `neg one`, by the parity of `j`, scaling the entry as the point interval `[s, s]`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.det : {d : ℕ} → (Fin (d + 1) → Fin (d + 1) → Taylm 𝕋 n) → Taylm 𝕋 n
  | 0, A => A 0 0
  | _ + 1, A =>
    Taylm.sum fun j =>
      let s : 𝕋 := if (j : ℕ) % 2 = 0 then one else neg one
      ((A 0 j).smul s s).times (Taylm.det fun i k => A i.succ (j.succAbove k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
