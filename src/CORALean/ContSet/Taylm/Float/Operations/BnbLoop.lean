import CORALean.ContSet.Taylm.Float.Operations.BnbStep
import CORALean.ContSet.Taylm.Float.Operations.ListMax
import CORALean.ContSet.Taylm.Float.Operations.ListMin

/-!
# `Taylm.bnbLoop`, over a floating-point scalar

The iteration of the listing: bound the union of the boxes, step, and stop once neither end moved
by more than `2ε` times the radius, or when `fuel` runs out. The float comparison is `le`, which
certifies a `true` only; the bounds stay sound for every stopping rule.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.bnbLoop (bnd : (Fin n → 𝕋 × 𝕋) → 𝕋 × 𝕋) (ε : 𝕋) :
    ℕ → List (Fin n → 𝕋 × 𝕋) → 𝕋 × 𝕋
  | 0, l => (Taylm.listMin (fun B => (bnd B).1) l, Taylm.listMax (fun B => (bnd B).2) l)
  | fuel + 1, l =>
    -- 7: the previous union
    let prev := (Taylm.listMin (fun B => (bnd B).1) l, Taylm.listMax (fun B => (bnd B).2) l)
    let l₁ := Taylm.bnbStep bnd l
    -- 30: the new union
    let cur := (Taylm.listMin (fun B => (bnd B).1) l₁, Taylm.listMax (fun B => (bnd B).2) l₁)
    -- 31: stop once neither end moved by more than `2ε·rad`
    let tol := mulUp (addUp ε ε) (half (subUp cur.2 cur.1))
    if le (absolute (subUp prev.2 cur.2)) tol = true ∧
        le (absolute (subUp cur.1 prev.1)) tol = true then cur
    else Taylm.bnbLoop bnd ε fuel l₁
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
