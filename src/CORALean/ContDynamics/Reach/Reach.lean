import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.SetUnion.SetUnion

/-!
# One reachability interface, over every system class

CORA's `reach`, read as a class the way `Mtimes` and `Enclose` are: `reachExact`
is what a system's dynamics actually reach, a `Set` and nothing an
implementation may widen; `reach` is what a representation computes for it,
`none` where the algorithm could not certify its own soundness conditions at
run time — CORA's failure mode, as when a linearization region does not contain
the set computed in it; `reach_outer` encloses the first in every result.

`Params` bundles what an algorithm needs beyond the initial set, every side
condition a `Prop` field of it or checked at run time, so `reach_outer` asks for
nothing beyond `sys`, `p` and `X₀`. One plain `Type`, not indexed by `n` or `S`:
a system whose algorithm needs a per-dimension datum (an input set) carries it
in `Sys` instead. `Sys` is universe-polymorphic, as `Enclose`'s layer kind is: a
closed-loop system stores a `NeuralNetwork`, which sits in `Type 1`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- `reachExact` is the exact set a system's dynamics reach; `reach` is what a
representation computes for it, `none` if it could not certify itself;
`reach_outer` is the enclosure between them, at every result `reach` returns. -/
class Reach (Sys : ℕ → Type u) (Params : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  reachExact {n : ℕ} : Sys n → Params → Set (Vec ℝ n) → Set (Vec ℝ n)
  reach {n : ℕ} : Sys n → Params → S n → Option (SetUnion (S n))
  reach_outer {n : ℕ} (sys : Sys n) (p : Params) (X₀ : S n) :
    ∀ R ∈ reach sys p X₀, reachExact sys p (construct X₀) ⊆ construct R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
