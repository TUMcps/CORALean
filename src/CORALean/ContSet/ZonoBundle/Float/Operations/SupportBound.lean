module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope

@[expose] public section

/-!
# The tightest of a float bundle's member bounds

The intersection sits inside every member, so any member's `Zonotope.boundDot`
bounds it too — soundness needs no choice at all. `minimum` only says which,
and being exact it rounds nothing, so what the fold returns denotes the least
of the members' bounds and costs no width.

Needs `0 < zB.k`, as `SetIntersection.isCompact_construct` needs a member, and for the same
reason: at `k = 0` the bundle is the whole space, unbounded in every nonzero direction.

## Inputs
* `zB` – float zonotope bundle
* `c` – linear functional
* `a` – float weights of the functional

## Hypotheses
* `hk` – the bundle has a member
* `hc` – the functional is the weighted sum

## Output
* the tightest of the members' upper bounds
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The least of `b` and a family, folded right as `sumUp` is, as the loop the compiler runs.
`minimumOver` would not do: it folds from `zero`, so it returns at most `zero`. -/
def ZonoBundle.aux_minimumFrom {k : ℕ} (b : 𝕋) (u : Fin k → 𝕋) : 𝕋 :=
  Fin.foldr k (fun i acc => minimum (u i) acc) b


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least of the members' own bounds. Any one of them is already sound, so
`hk` buys the *value*, not the proof: an empty family has no member to read. -/
def ZonoBundle.boundDot (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 zB.construct c where
  val := ZonoBundle.aux_minimumFrom (Zonotope.boundDot (zB.Z ⟨0, hk⟩) a hc).val
    fun i => (Zonotope.boundDot (zB.Z i) a hc).val
  le x hx := by
    -- anything under `b` and under every entry is under the fold, `minimum` being exact
    have hle : ∀ {k : ℕ} {b : 𝕋} {u : Fin k → 𝕋} {x : ℝ},
        x ≤ toReal b → (∀ j, x ≤ toReal (u j)) →
        x ≤ toReal (ZonoBundle.aux_minimumFrom b u) := by
      intro k
      induction k with
      | zero => intro b u x hb _; exact hb
      | succ m ih =>
        intro b u x hb hu
        rw [ZonoBundle.aux_minimumFrom, Fin.foldr_succ, toReal_minimum]
        exact le_min (hu 0) (ih hb fun j => hu j.succ)
    have hmem : ∀ i, x ∈ (zB.Z i).construct := fun i => SetIntersection.mem_construct_ofFn.mp hx i
    exact hle ((Zonotope.boundDot (zB.Z ⟨0, hk⟩) a hc).le x (hmem _))
      fun i => (Zonotope.boundDot (zB.Z i) a hc).le x (hmem i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
