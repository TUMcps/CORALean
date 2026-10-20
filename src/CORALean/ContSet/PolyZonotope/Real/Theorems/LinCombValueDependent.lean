module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombValue

@[expose] public section

/-!
# A point of `linComb` read back as a segment, where the operands are dependent

`linComb_value` evaluates a chosen witness; this reads the other way. Given *any* factor vector
of `linComb`, the point it names is the segment point at `λ = (1+α)/2` between the two
operands' points at their own factors, the reverse inclusion of [1, Prop. 14] (`⊆` being
`linComb_outer`). `q = 0` on both operands makes the reading exact: with no independent block
there is nothing left to enclose. Stated apart from the set equality so that `ConPolyZono`
can reach it at `toPolyZonotope`: `exact` unfolds the projections.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values of the combination
* `β` – independent values of the combination

## Hypotheses
* `h₁` – first has no independent generators
* `h₂` – second has no independent generators

## Conclusion
* the combination point reads back as a segment point

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The factor vector of `linComb`, taken apart into the two operands' own
factors and the fresh one and appended back together. -/
theorem PolyZonotope.aux_append_linComb_p {pZ₁ pZ₂ : PolyZonotope α}
    (a : Fin (pZ₁.linComb pZ₂).p → ℝ) {v : ℝ}
    (hv : a (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1)) = v) : -- --- CONCL ---
    Fin.append (Fin.append (fun k => a (Fin.castAdd 1 (Fin.castAdd pZ₂.p k)))
          (fun k => a (Fin.castAdd 1 (Fin.natAdd pZ₁.p k))))
        (fun _ : Fin 1 => v) = a := by -- --- PROOF ---
  -- the two operands' factors reassemble into the head of the vector
  have hin : Fin.append (fun k => a (Fin.castAdd 1 (Fin.castAdd pZ₂.p k)))
      (fun k => a (Fin.castAdd 1 (Fin.natAdd pZ₁.p k)))
      = fun i => a (Fin.castAdd 1 i) :=
    Fin.append_castAdd_natAdd (f := fun i => a (Fin.castAdd 1 i))
  -- and the fresh factor is the single entry past them
  have hout : (fun _ : Fin 1 => v) = fun i : Fin 1 => a (Fin.natAdd (pZ₁.p + pZ₂.p) i) := by
    funext i
    rw [Subsingleton.elim i (0 : Fin 1), hv]
  rw [hin, hout]
  exact Fin.append_castAdd_natAdd

omit [AddCommGroup α] [Module ℝ α] in
/-- `linComb` keeps no independent generator where neither operand had one, so
every sum over an independent block below is empty. -/
theorem PolyZonotope.aux_isEmpty_dependent_q {pZ₁ pZ₂ : PolyZonotope α}
    (h₁ : pZ₁.q = 0) (h₂ : pZ₂.q = 0) : IsEmpty (Fin (pZ₁.q + pZ₂.q)) := by
  have hq : pZ₁.q + pZ₂.q = 0 := by omega
  rw [hq]
  infer_instance


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `linComb` is the segment point at `λ = (1+α)/2` between the
two operands' points at their own factors, where neither operand has an
independent generator. -/
theorem PolyZonotope.linComb_value_dependent (pZ₁ pZ₂ : PolyZonotope α)
    (h₁ : pZ₁.q = 0) (h₂ : pZ₂.q = 0) (a : Fin (pZ₁.linComb pZ₂).p → ℝ)
    (β : Fin (pZ₁.linComb pZ₂).q → ℝ) : -- --- CONCL ---
    (pZ₁.linComb pZ₂).c
        + ∑ i, PolyZonotope.monomial (pZ₁.linComb pZ₂).E a i • (pZ₁.linComb pZ₂).G i
        + ∑ j, β j • (pZ₁.linComb pZ₂).GI j
      = ((1 + a (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1))) / 2)
          • (pZ₁.c + ∑ i, PolyZonotope.monomial pZ₁.E
                (fun k => a (Fin.castAdd 1 (Fin.castAdd pZ₂.p k))) i • pZ₁.G i
              + ∑ j, (0 : ℝ) • pZ₁.GI j)
        + (1 - (1 + a (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1))) / 2)
          • (pZ₂.c + ∑ i, PolyZonotope.monomial pZ₂.E
                (fun k => a (Fin.castAdd 1 (Fin.natAdd pZ₁.p k))) i • pZ₂.G i
              + ∑ j, (0 : ℝ) • pZ₂.GI j) := by -- --- PROOF ---
  haveI hq : IsEmpty (Fin (pZ₁.q + pZ₂.q)) := PolyZonotope.aux_isEmpty_dependent_q h₁ h₂
  haveI : IsEmpty (Fin (pZ₁.linComb pZ₂).q) := hq
  -- the witness `linComb_value` evaluates is this vector's own three pieces
  have hval := PolyZonotope.linComb_value pZ₁ pZ₂
    (fun k => a (Fin.castAdd 1 (Fin.castAdd pZ₂.p k))) (fun _ => (0 : ℝ))
    (fun k => a (Fin.castAdd 1 (Fin.natAdd pZ₁.p k))) (fun _ => (0 : ℝ))
    ((1 + a (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1))) / 2)
  have hv : a (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1))
      = 2 * ((1 + a (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1))) / 2) - 1 := by ring
  rw [PolyZonotope.aux_append_linComb_p a hv] at hval
  rw [hval]
  -- what is left is the two independent blocks, both empty
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
