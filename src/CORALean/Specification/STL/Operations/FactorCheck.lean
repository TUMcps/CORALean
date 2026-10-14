module

public import CORALean.Specification.STL.Operations.FactorStep

@[expose] public section

/-!
# [1, Alg. 2]: the model checking by unsafe factors

The list `L` of polytopes of factors `α̃ ∈ [-1, 1]^p` (`box`) that may violate the
specification, one polytope list `V` per conjunction `h` of the reachset formula
`⋀_h ⋁_j ⋁_k (R̃(jΔt/2) ∩ ⋃_l P_hjkl = ∅)` of [1, Eq. (12)]; the system satisfies it if `L = []`.
`R j` is `R̃(jΔt/2)`, `P h j k` the list of the `P_hjkl`, and the others as for `STL.factorStep`.
Lines 1-2, the reachable set and the conversion to RTL, are the arguments. Lines 6-13 loop over
`j` and `k`, here over the list of pairs `(j, k)`, each pass `STL.factorStep`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the polytopes `L` of the factors that may violate the formula. -/
def STL.factorCheck (H J K : ℕ) (box : Set X) (R : ℕ → Set S) (P : ℕ → ℕ → ℕ → List (Set S))
    (unsafeSet : ℕ → Set S → Set X) (meets : Set S → Set S → Bool) (isEmpty : Set X → Bool) :
    List (Set X) :=
  -- 3. `L ← ∅`
  let L₀ : List (Set X) := []
  -- 6. the pairs `(j, k)`, `j` from 0 to `J` and `k` from 0 to `K`
  let jk := (List.range (J + 1)).flatMap fun j => (List.range (K + 1)).map fun k => (j, k)
  -- 4. `for h ← 0 to H do`, carrying `L`
  (List.range (H + 1)).foldl (fun L h =>
    -- 5. `V ← [-1, 1]^p`
    let V₀ : List (Set X) := [box]
    -- 6. `for j, k`: lines 7-13, here `STL.factorStep`
    let V := jk.foldl (fun V (j, k) =>
      STL.factorStep (R j) (P h j k) (unsafeSet j) meets isEmpty V) V₀
    -- 14. `L ← (L, V)`
    L ++ V) L₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
