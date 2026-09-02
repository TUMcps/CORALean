import CORALean.ContSet.ContSet.ContSet

/-!
# What a layer is

CORA's `nnLayer`: what the layer computes on a point, what it computes on a set,
and the one obligation tying the two together — the propagated set contains the
image of the exact one. Everything downstream is that obligation composed with
itself.

A layer is a structure and not a class because a network holds many of them at
once and they are told apart by their weights, not by their types. It carries
its own soundness proof as a field, so a network is a list of layers with
nothing left to check: constructing the layer is what discharges the obligation,
and `Layers/` is where the concrete ones do it.

`eval` is a function of a point rather than a relation, which is what makes the
obligation an image inclusion. A layer whose behaviour is genuinely set-valued —
a rounded implementation, a nondeterministic activation — is one of these at the
function it refines, and pays the difference into `propagate`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}

structure Layer (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m : ℕ) where
  eval : Vec ℝ n → Vec ℝ m
  propagate : S n → S m
  propagate_outer (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s) :
    eval x ∈ construct (propagate s)

/-- The obligation as an inclusion, which is the form it composes in. -/
theorem Layer.image_subset (L : Layer S n m) (s : S n) :
    L.eval '' construct s ⊆ construct (L.propagate s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact L.propagate_outer s x hx

/-- Carries a coordinate past a block untouched, which is how a skip connection
is written: the skipped coordinates travel in the same set as the rest, so the
dependency between them survives. -/
def Layer.identity (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) : Layer S n n where
  eval x := x
  propagate s := s
  propagate_outer _ _ hx := hx

/-- Applied right to left, as composition is written. -/
def Layer.comp (L₂ : Layer S m k) (L₁ : Layer S n m) : Layer S n k where
  eval x := L₂.eval (L₁.eval x)
  propagate s := L₂.propagate (L₁.propagate s)
  propagate_outer s x hx := L₂.propagate_outer _ _ (L₁.propagate_outer s x hx)

end CORALean.Real
