module

public import CORALean.ContSet.ConZonotope.Real.Theorems.LiftIff
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.Global.Block

@[expose] public section

/-!
# A constrained zonotope to halfspaces, through its lifted zonotope

[1, Prop. 3 (CG to H)] and the sentence after it: at the trivial partition, `m₁ = n_c`, `m₂ = 0`,
the lifted set `Z⁺ = {[G; A], [c; -b]}` is a zonotope, "which gives the conversion CG → H by
converting `Z⁺`". Any halfspace description `P` of `Z⁺` gives one of `Z`. Since `z ∈ Z` iff
`[z; 0] ∈ Z⁺` (`mem_iff_append_mem_lift`), `Z` is `P` read on the subspace `y = 0`. That is
`P.comap` along `z ↦ [z; 0]`: the same right-hand sides, each row restricted to its first `n`
coefficients.

Where `Z⁺`'s generators span, `Zonotope.hRep_eq` (Althoff et al. NAHS'10 `Thm. 7`) is such a
`P`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3 (CG to H)]: an H-representation `P` of the lifted zonotope `Z⁺` gives one of `Z`,
`P` restricted to `y = 0`. -/
theorem ConZonotope.construct_eq_comap_of_lift {n m h : ℕ} (c : Vec ℝ n)
    (G : Fin h → Vec ℝ n) (A : Mat ℝ (m + 0) h) (b : Vec ℝ (m + 0))
    (P : HPolytope (Vec ℝ (n + m)))
    (hP : P.construct = (ConZonotope.lift (m₂ := 0) c G A b).construct) : -- --- STMT ---
    (ConZonotope.ofMat c G A b).construct
      = (P.comap (blockPadLeft n m)).construct := by -- --- PROOF ---
  ext z
  rw [HPolytope.comap_exact, Set.mem_preimage, hP]
  exact ConZonotope.mem_iff_append_mem_lift c G A b z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
