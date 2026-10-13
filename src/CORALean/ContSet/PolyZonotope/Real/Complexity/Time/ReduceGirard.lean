import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.ReduceBy
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirard

/-!
# `PolyZonotope.reduceGirardCost`

Asserted, not proved, by reading `Operations/ReduceGirard.lean`. Girard's
metric on one generator is `n` absolute values and `n - 1` additions for `‖g‖₁`,
`n` more and `n` comparisons for the `max` fold, and one negation for the
descending sort key: at most `4 * n + 2` each, as in `Zonotope`'s own file. It
is evaluated on the concatenation for the joint rank and again on each block for
its split, so twice over `h + q` bounds it.

Three sorts follow — the joint one and one per block — each bounded by
`Cost.sort` at the joint width; `aux_girardKeptDep` then counts the dependent
ranks, `h` comparisons and a `min`. Last is `reduceBy`, absorbing at most the
whole of either block.

No order argument: below `o * n` the operation is the identity and costs
nothing, and above it the absorbed blocks are `h` and `q` wide at worst either
way, so this bounds every `o` at once.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduceGirard` costs at `Vec ℝ n` on `h` dependent and
`q` independent generators: the metrics, the sorts, the count, the absorption. -/
def PolyZonotope.reduceGirardCost (n h q : ℕ) : Cost :=
  ⟨(h + q) * (8 * n + 4) + (h + q) + 1⟩ + 3 • Cost.sort (h + q)
    + PolyZonotope.reduceByCost n h q

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.reduceGirardCost_mono {h h' q q' : ℕ} (n : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.reduceGirardCost n h q
      ≤ PolyZonotope.reduceGirardCost n h' q' := by -- --- PROOF ---
  -- the joint width is what every term but the last is stated in
  have hs : h + q ≤ h' + q' := Nat.add_le_add hh hq
  refine Cost.add_le_add (Cost.add_le_add ?_ ?_) (PolyZonotope.reduceByCost_mono n hh hq)
  · exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hs) hs) le_rfl
  · exact Nat.mul_le_mul_left _ (Cost.sort_mono hs)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
