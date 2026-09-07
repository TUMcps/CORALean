import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope

/-!
# The tightest of a float bundle's member bounds

The intersection sits inside every member, so any member's `Zonotope.boundDot`
bounds it too — soundness needs no choice at all. `minimum` only says which,
and being exact it rounds nothing, so what the fold returns denotes the least
of the members' bounds and costs no width.

Needs `0 < zB.k`, as `isCompact_construct` does and for the same reason: at
`k = 0` the bundle is the whole space, unbounded in every nonzero direction.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The least of `b` and a family, right-nested as `sumUp` is. `minimumOver`
would not do: it folds from `zero`, so it returns at most `zero`. -/
def ZonoBundle.aux_minimumFrom : {k : ℕ} → 𝕋 → (Fin k → 𝕋) → 𝕋
  | 0, b, _ => b
  | _ + 1, b, u => minimum (u 0) (ZonoBundle.aux_minimumFrom b fun i => u i.succ)

/-- Anything under `b` and under every entry is under the fold, `minimum` being
exact. This is the whole of what the bound below owes. -/
theorem ZonoBundle.aux_le_minimumFrom : ∀ {k : ℕ} {b : 𝕋} {u : Fin k → 𝕋} {x : ℝ},
    x ≤ toReal b → (∀ j, x ≤ toReal (u j)) →
    x ≤ toReal (ZonoBundle.aux_minimumFrom b u) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro b u x hb _; exact hb
  | succ m ih =>
    intro b u x hb hu
    rw [ZonoBundle.aux_minimumFrom, toReal_minimum]
    exact le_min (hu 0) (ih hb fun j => hu j.succ)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least of the members' own bounds. Any one of them is already sound, so
`hk` buys the *value*, not the proof: an empty family has no member to read. -/
def ZonoBundle.boundDot (zB : ZonoBundle 𝕋 n) (hk : 0 < zB.k) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 zB.construct c where
  val := ZonoBundle.aux_minimumFrom ((zB.Z ⟨0, hk⟩).boundDot a hc).val
    fun i => ((zB.Z i).boundDot a hc).val
  le x hx := by
    have hmem : ∀ i, x ∈ (zB.Z i).construct := fun i => Set.mem_iInter.mp hx i
    exact ZonoBundle.aux_le_minimumFrom (((zB.Z ⟨0, hk⟩).boundDot a hc).le x (hmem _))
      fun i => ((zB.Z i).boundDot a hc).le x (hmem i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
