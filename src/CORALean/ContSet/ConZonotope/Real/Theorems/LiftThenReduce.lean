import CORALean.ContSet.ConZonotope.Real.Theorems.LiftIff

/-!
# Lift-then-reduce is an enclosure

[1, Sec. 4.3, eq. 30]: lift `Z = {G, c, A, b}` to the zonotope `Z⁺ = {[G; A], [c; −b]}`, enclose
that by `Z̃⁺ = {[G̃; Ã], [c; −b]}` (the paper uses a zonotopic order reduction, with fewer
generators), and read `Z̃⁺` back as `Z̃ = {G̃, c, Ã, b}`: then `Z ⊂ Z̃`, by two applications of
Prop. 3. The reduction itself is a hypothesis here; its construction, after Chisci et al., is not
formalized.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3]: `Z⁺ ⊂ Z̃⁺` gives `Z ⊂ Z̃`, for any `G̃`, `Ã` with `h'` columns. -/
theorem ConZonotope.lift_then_reduce_outer {n m h h' : ℕ} (c : Vec ℝ n)
    (G : Fin h → Vec ℝ n) (A : Mat ℝ (m + 0) h) (b : Vec ℝ (m + 0))
    (G' : Fin h' → Vec ℝ n) (A' : Mat ℝ (m + 0) h')
    (hlift : (ConZonotope.lift (m₂ := 0) c G A b).construct
      ⊆ (ConZonotope.lift (m₂ := 0) c G' A' b).construct) :
    (ConZonotope.ofMat c G A b).construct ⊆ (ConZonotope.ofMat c G' A' b).construct :=
  fun _ hz =>
    (ConZonotope.mem_iff_append_mem_lift (m₂ := 0) c G' A' b _).mpr
      (hlift ((ConZonotope.mem_iff_append_mem_lift (m₂ := 0) c G A b _).mp hz))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
