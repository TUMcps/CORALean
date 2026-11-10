module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Data.Erased

@[expose] public section

/-!
# The layer interface

One class per *kind* of layer: `Enclose Layer ContSet` is to the weights `L : Layer n m` of a
kind what `Mtimes` is to a matrix. `enclose` propagates, `eval` is the function over ℝ it encloses,
and `enclose_outer` is proved once per kind for all weights, a hypothesis on the weights riding
along as a `Prop` field of them. `eval` is `Erased`: `Erased.mk` is `macro_inline`, so its argument
lands in a closure returning a `Prop`, is erased, and is never compiled, and only the noncomputable
`Erased.out`, in proofs, reads it back. So an instance whose `eval` is `Real.exp`-built still runs.
Each kind's instance is in `Instances.lean`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSetLike


-- ========================================  MAIN TYPE  ========================================= --

/-- A kind's enclosure: `enclose` on its weights, the function `eval` it encloses, held `Erased`,
and the guarantee, proved once for all weights. -/
class Enclose (Layer : ℕ → ℕ → Type u) (ContSet : ℕ → Type)
    [∀ n, ContSetLike (ContSet n) (Vec ℝ n)] where
  eval {n m : ℕ} : Layer n m → Erased (Vec ℝ n → Vec ℝ m)
  enclose {n m : ℕ} : Layer n m → ContSet n → ContSet m
  enclose_outer {n m : ℕ} (L : Layer n m) (S : ContSet n) :
    (eval L).out '' toSet S ⊆ toSet (enclose L S)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
