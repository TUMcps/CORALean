import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.SetUnion.SetUnion

/-!
# One reachability interface, over every system class

CORA's `reach`, read as a class the way `Mtimes` and `Enclose` are: `reachExact`
is what a system's dynamics actually reach, a `Set` and nothing an
implementation may widen; `reach` is what a representation computes, a
`SetUnion` since an algorithm's own steps are already several sets rather than
one; `reach_outer` is the guarantee tying the two together.

`Params` bundles whatever a system's algorithm needs beyond the initial set —
a time horizon, a truncation order, a zonotope order — with every side
condition a `Prop` field of it, so `reach_outer` asks for nothing beyond
`sys`, `p` and `X₀`. It is one plain `Type`, not indexed by `n` or by `S`, so
it cannot hold a per-dimension representation; a system whose algorithm needs
one (an input set) is bundled with it in `Sys` instead, at each instance.

`Sys` is universe-polymorphic, as `Enclose`'s layer kind is: a closed-loop
system stores a `NeuralNetwork`, which sits in `Type 1` for the same reason
`Enclose` does, so `Sys n : Type` alone would shut every such system out.
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
representation computes for it; `reach_outer` is the enclosure between them. -/
class Reach (Sys : ℕ → Type u) (Params : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  reachExact {n : ℕ} : Sys n → Params → Set (Vec ℝ n) → Set (Vec ℝ n)
  reach {n : ℕ} : Sys n → Params → S n → SetUnion (S n)
  reach_outer {n : ℕ} (sys : Sys n) (p : Params) (X₀ : S n) :
    reachExact sys p (construct X₀) ⊆ construct (reach sys p X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
