module

public import CORALean.ContSet.Zonotope.Float.Operations.Minnorm
public import CORALean.ContSet.Zonotope.Float.Theorems.MinnormOffsetGe

@[expose] public section

/-!
# No larger ball fits

A Euclidean ball around the center that lies in the zonotope the stored floats describe has radius
at most the `Zonotope.minnorm` that is computed: the radius is at most every rounded offset
(`minnormOffset_ge`), hence at most their minimum. This is the float counterpart of
`Zonotope.le_minnorm_of_ball_subset`, and needs no spanning hypothesis: it is a statement about
balls, whichever rows the rounded cross products gave.

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnorm_ball (p : ℕ) (Z : Zonotope (Vec 𝕋 (n + 1))) (U : 𝕋)
    (hU : Z.minnorm p = some U) (r : ℝ) (hr : 0 ≤ r)
    (hball : ∀ y : Vec ℝ (n + 1), y ⬝ᵥ y ≤ r ^ 2 → toRealVec Z.c + y ∈ nominalSet Z) :
    r ≤ toReal U := by -- --- PROOF ---
  unfold Zonotope.minnorm at hU
  dsimp only at hU
  -- every row of `b` is above `r`
  have hrows : ∀ o ∈ (List.sublistsLen n (List.finRange Z.h)).filterMap (fun T =>
      if hT : T.length = n then Z.minnormOffset p fun k => T.get (k.cast hT.symm) else none),
      r ≤ toReal o := by
    intro o ho
    obtain ⟨T, -, hT⟩ := List.mem_filterMap.mp ho
    split_ifs at hT with hlen
    exact Zonotope.minnormOffset_ge p Z _ o hT r hr hball
  -- and a fold of `minimum` over such rows stays above it
  have key : ∀ (l : List 𝕋) (best : Option 𝕋), (∀ o ∈ l, r ≤ toReal o) →
      (∀ x, best = some x → r ≤ toReal x) →
      ∀ V, l.foldl (fun best o => match best with
        | none => some o
        | some x => some (minimum x o)) best = some V → r ≤ toReal V := by
    intro l
    induction l with
    | nil => intro best _ hb V hV; exact hb V hV
    | cons o t ih =>
      intro best hl hb V hV
      -- the accumulator after the head is above `r`, by the minimum of two such numbers
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
