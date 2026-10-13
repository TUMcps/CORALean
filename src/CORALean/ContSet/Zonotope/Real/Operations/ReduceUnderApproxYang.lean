module

public import CORALean.ContSet.Zonotope.Real.Operations.CombineGens

@[expose] public section

/-!
# `Zonotope.reduceUnderApproxYang`

CORA's `reduceUnderApprox(Z, 'yang', order)`, [1, Sec. IV-B.1]: replace two generators
by their sum or difference ([1, Prop. 6], `combineGens`) until at most `N` remain, one
generator fewer per step. Which pair and which sign is [1]'s heuristic (15) — the pair
minimizing `‖gᵢ‖‖gⱼ - ĝᵢgⱼᵀĝᵢ‖` and the sign whose result is the more perpendicular
to the rest — and is `sel`'s choice here; containment holds for every choice, so the
heuristic is a parameter rather than part of the guarantee. CORA's `N` is
`order · dim(Z)`.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Combine the pair `sel` picks, `Z.h - N` times or until fewer than two generators
are left. -/
def Zonotope.reduceUnderApproxYang
    (sel : (Z : Zonotope α) → {m : ℕ} → Z.h = m + 2 → Fin (m + 2) × Fin (m + 1) × Bool)
    (N : ℕ) (Z : Zonotope α) : Zonotope α :=
  let rec go : ℕ → Zonotope α → Zonotope α
    | 0, Z => Z
    | k + 1, Z =>
      match hm : Z.h with
      | _ + 2 =>
        let (i, j, add) := sel Z hm                      -- the pair by (15)
        go k (Z.combineGens hm i j add)                  -- [1, Prop. 6]
      | _ => Z
  go (Z.h - N) Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
