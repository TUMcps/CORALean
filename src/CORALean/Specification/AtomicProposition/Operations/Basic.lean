module

public import CORALean.Specification.AtomicProposition.AtomicProposition

@[expose] public section

/-!
# `AtomicProposition/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =============================  `AtomicProposition.containsLoc`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `out = containsLoc(ap,loc)`: every location is allowed when `locs` is empty. CORA writes the
membership as `in(ap.locs,loc)`, read here as membership of the list. -/
def AtomicProposition.containsLoc (ap : AtomicProposition S n) (loc : ℕ) : Bool :=
  if ap.locs ≠ [] then ap.locs.contains loc else true


-- ================================  `AtomicProposition.ofSet`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ap = atomicProposition(set)`: `dims = 1:dim(set)` and `locs = []`. -/
def AtomicProposition.ofSet (set : S n) : AtomicProposition S n :=
  ⟨n, set, id, []⟩


-- ==============================  `AtomicProposition.readPoint`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `point(ap.dims)`: the coordinates of the proposition, read from a point of the ambient space. -/
def AtomicProposition.readPoint {α : Type} (ap : AtomicProposition S n) (x : Fin n → α) :
    Fin ap.k → α :=
  fun i => x (ap.dims i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
