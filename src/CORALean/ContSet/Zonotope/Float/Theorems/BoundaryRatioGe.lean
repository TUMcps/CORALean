module

public import CORALean.ContSet.Zonotope.Float.Operations.BoundaryRatio
public import CORALean.ContSet.Zonotope.Float.Theorems.BoundaryRatioAtGe

@[expose] public section

/-!
# No larger step stays in the zonotope

A step `t >= 0` with `startPoint + t * dir` in the zonotope the stored floats describe is at most
the `Zonotope.boundaryRatio` that is computed: it is at most every facet row's bound
(`boundaryRatioAt_ge`), hence at most their minimum. The statement needs no spanning hypothesis:
the rows may be any rounded vectors, and each is a valid bound.

Source: [1, Thm. 2].

## Inputs
* `Z` – zonotope
* `dir` – direction
* `start` – starting point
* `t` – step length

## Hypotheses
* `ht` – step nonnegative
* `hmem` – stepped point lies in the nominal zonotope

## Conclusion
* step is at most every returned bound

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.boundaryRatio_ge (Z : Zonotope (Vec 𝕋 (n + 1))) (dir start : Vec 𝕋 (n + 1)) (t : ℝ)
    (ht : 0 ≤ t) (hmem : toRealVec start + t • toRealVec dir ∈ nominalSet Z) :
    ∀ U ∈ Z.boundaryRatio dir start,
      t ≤ toReal U := by -- --- PROOF ---
  intro U (hU : Z.boundaryRatio dir start = some U)
  unfold Zonotope.boundaryRatio at hU
  dsimp only at hU
  -- every row of `b` is above `t`
  have hrows : ∀ o ∈ (List.sublistsLen n (List.finRange Z.h)).filterMap (fun T =>
      if hT : T.length = n then Z.boundaryRatioAt dir start fun k => T.get (k.cast hT.symm)
      else none), t ≤ toReal o := by
    intro o ho
    obtain ⟨T, -, hT⟩ := List.mem_filterMap.mp ho
    split_ifs at hT with hlen
    exact Zonotope.boundaryRatioAt_ge Z dir start _ t ht hmem o hT
  -- and a fold of `minimum` over such rows stays above it
  have key : ∀ (l : List 𝕋) (best : Option 𝕋), (∀ o ∈ l, t ≤ toReal o) →
      (∀ x, best = some x → t ≤ toReal x) →
      ∀ V, l.foldl (fun best o => match best with
        | none => some o
        | some x => some (minimum x o)) best = some V → t ≤ toReal V := by
    intro l
    induction l with
    | nil => intro best _ hb V hV; exact hb V hV
    | cons o l ih =>
      intro best hl hb V hV
      -- the accumulator after the head is above `t`: the head, or the minimum of two such numbers
      refine ih _ (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) ?_ V hV
      intro x hx
      cases best with
      | none =>
        simp only [Option.some.injEq] at hx
        exact hx ▸ hl o List.mem_cons_self
      | some y =>
        simp only [Option.some.injEq] at hx
        rw [← hx, toReal_minimum]
        exact le_min (hb y rfl) (hl o List.mem_cons_self)
  exact key _ none hrows (fun x hx => absurd hx (by simp)) U hU

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
