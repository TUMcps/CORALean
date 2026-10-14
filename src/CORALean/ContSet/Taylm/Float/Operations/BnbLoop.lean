module

public import CORALean.ContSet.Taylm.Float.Operations.BnbStep
public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# `Taylm.bnbLoop`, over a floating-point scalar

The iteration of the listing: bound the union of the boxes, step, and stop once neither end moved
by more than `2ε` times the radius, or when `fuel` runs out. The float comparison is `le`, which
certifies a `true` only; the bounds stay sound for every stopping rule.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.bnbLoop (bnd : (Fin n → Interval 𝕋) → Interval 𝕋) (ε : 𝕋) :
    ℕ → List (Fin n → Interval 𝕋) → Interval 𝕋
  | 0, l => ⟨Taylm.listMin (fun B => (bnd B).inf) l, Taylm.listMax (fun B => (bnd B).sup) l⟩
  | fuel + 1, l =>
    -- 7: the previous union
    let prev : Interval 𝕋 := ⟨Taylm.listMin (fun B => (bnd B).inf) l,
        Taylm.listMax (fun B => (bnd B).sup) l⟩
    let l₁ := Taylm.bnbStep bnd l
    -- 30: the new union
    let cur : Interval 𝕋 := ⟨Taylm.listMin (fun B => (bnd B).inf) l₁,
        Taylm.listMax (fun B => (bnd B).sup) l₁⟩
    -- 31: stop once neither end moved by more than `2ε·rad`
    let tol := mulUp (addUp ε ε) (half (subUp cur.sup cur.inf))
    if le (absolute (subUp prev.sup cur.sup)) tol = true ∧
        le (absolute (subUp cur.inf prev.inf)) tol = true then cur
    else Taylm.bnbLoop bnd ε fuel l₁
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
