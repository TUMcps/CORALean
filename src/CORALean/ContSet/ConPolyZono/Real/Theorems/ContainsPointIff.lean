import CORALean.ContSet.ConPolyZono.Real.Operations.ContainsPoint
import CORALean.ContSet.ConPolyZono.Real.Theorems.MemExtPolyZonotopeIff

/-!
# `[p; 0]` is in the extended polynomial zonotope iff `p` is in the set

With a point `b` (`b.inf = b.sup`, CORA's vector), `-b + A μ(α)` is zero exactly when the constraint
`A μ(α) = b` holds, and the first coordinates are the generators' own: `[p; 0] ∈ pZ` iff
`p ∈ cPZ`. This is what `@conPolyZono/contains_` means to decide for a numeric operand.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.containsPoint_iff (cPZ : ConPolyZono (Vec ℝ n)) (hb : cPZ.b.inf = cPZ.b.sup)
    (p : Vec ℝ n) : cPZ.containsPoint p ↔ p ∈ cPZ.construct := by -- --- PROOF ---
  unfold ConPolyZono.containsPoint
  rw [ConPolyZono.mem_extPolyZonotope_iff]
  constructor
  · -- a zero residual is the constraint at both ends of the degenerate interval
    rintro ⟨a, β, ha, hβ, hc, hx⟩
    refine ⟨a, β, ha, hβ, fun i => ?_, hx⟩
    refine ⟨?_, ?_⟩
    · have := hc i
      simp at this
      linarith
    · have := hc i
      simp at this
      rw [← hb]
      linarith
  · -- and the constraint at a point `b` is a zero residual
    rintro ⟨a, β, ha, hβ, hs, hx⟩
    refine ⟨a, β, ha, hβ, fun i => ?_, hx⟩
    have h1 := (hs i).1
    have h2 := (hs i).2
    rw [← hb] at h2
    simp
    linarith


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
