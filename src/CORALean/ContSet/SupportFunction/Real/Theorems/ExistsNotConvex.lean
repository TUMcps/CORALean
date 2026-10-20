module

public import CORALean.ContSet.SupportFunction.Real.Theorems.IsClosed
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# A convex set that is no support function

A support function denotes a closed set (`SupportFunction.isClosed_construct`), so the open
interval `(0, 1)`, which is convex, is the set of none: it shares its support function with
`[0, 1]`. What a support function represents is the closed convex sets, not all convex ones,
where the introduction of [1] says "all convex sets".

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a convex set that no support function denotes

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem SupportFunction.exists_convex_not_supportFunction : -- --- CONCL ---
    ∃ S : Set (Vec ℝ 1),
      Convex ℝ S ∧ ¬ ∃ F : SupportFunction (Vec ℝ 1), F.construct = S := by -- --- PROOF ---
  refine ⟨(fun x : Vec ℝ 1 => x 0) ⁻¹' Set.Ioo 0 1, ?_, ?_⟩
  · exact (convex_Ioo (0 : ℝ) 1).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  · rintro ⟨F, hF⟩
    -- the set is not closed: the point `0` is in its closure and not in it
    have hcl := F.isClosed_construct
    rw [hF] at hcl
    have hseq : Filter.Tendsto (fun k : ℕ => (fun _ => 1 / ((k : ℝ) + 1) : Vec ℝ 1))
        Filter.atTop (nhds 0) :=
      tendsto_pi_nhds.mpr fun _ => tendsto_one_div_add_atTop_nhds_zero_nat
    have h0 := hcl.mem_of_tendsto hseq (Filter.eventually_atTop.mpr ⟨1, fun k hk => by
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one (by positivity)]
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith⟩)
    exact absurd h0.1 (lt_irrefl _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
