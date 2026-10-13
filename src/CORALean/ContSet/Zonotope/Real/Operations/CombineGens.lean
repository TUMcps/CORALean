module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `Zonotope.combineGens`

[1, Prop. 6]'s reduction step: remove two generators `gᵢ`, `gⱼ` and append
`gᵢ + gⱼ` (`G₁`) or `gᵢ - gⱼ` (`G₂`), one generator fewer. `i` indexes `Z`'s
`m + 2` generators and `j` the `m + 1` left once `gᵢ` is out, so the pair is
distinct by construction; `hm` only lines the count up. The centre is kept.

Real layer only: a rounded `gᵢ ± gⱼ` is no combination of `gᵢ` and `gⱼ`, and the float
zonotope pays rounding outward, which an inner approximation cannot use.

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

/-- [1, Prop. 6]: `Z`'s generators without `gᵢ` and `gⱼ`, then `gᵢ + gⱼ` (`add`) or
`gᵢ - gⱼ` appended. -/
def Zonotope.combineGens (Z : Zonotope α) {m : ℕ} (hm : Z.h = m + 2) (i : Fin (m + 2))
    (j : Fin (m + 1)) (add : Bool) : Zonotope α :=
  let g : Fin (m + 2) → α := fun k => Z.G (Fin.cast hm.symm k)  -- G = [g₁, …, g_N]
  let gi := g i
  let gj := g (i.succAbove j)
  let rest : Fin m → α := fun k => g (i.succAbove (j.succAbove k))  -- G without gᵢ, gⱼ
  let gnew := if add then gi + gj else gi - gj
  ⟨m + 1, Z.c, Fin.snoc (α := fun _ => α) rest gnew⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
