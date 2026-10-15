module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Data.Erased

@[expose] public section

/-!
# The layer interface

One class per *kind* of layer: `Enclose L S` is to the weights `l : L n m` of a kind what
`Mtimes` is to a matrix. `enclose` propagates, `eval` is the function over ℝ it encloses, and
`enclose_outer` is proved once per kind for all weights, a hypothesis on the weights riding along
as a `Prop` field of them. `eval` is `Erased`: `Erased.mk` is `macro_inline`, so its argument
lands in a closure returning a `Prop`, is erased, and is never compiled, and only the
noncomputable `Erased.out`, in proofs, reads it back. So an instance whose `eval` is
`Real.exp`-built still runs. Each kind's instance is in `Instances.lean`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- A kind's enclosure: `enclose` on its weights, the function `eval` it encloses, held `Erased`,
and the guarantee, proved once for all weights. -/
class Enclose (L : ℕ → ℕ → Type u) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  eval {n m : ℕ} : L n m → Erased (Vec ℝ n → Vec ℝ m)
  enclose {n m : ℕ} : L n m → S n → S m
  enclose_outer {n m : ℕ} (l : L n m) (s : S n) :
    (eval l).out '' construct s ⊆ construct (enclose l s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
