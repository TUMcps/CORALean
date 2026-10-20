module

public import CORALean.ContSet.StarSet.Float.Operations.AbsorbRounding
public import CORALean.ContSet.StarSet.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.MemLiftNominalIff
public import CORALean.ContSet.Interval.Float.Theorems.MemAppendIff

@[expose] public section

/-!
# `StarSet.absorbRounding` holds the whole set in its nominal part

A point `c + Gα + e`, `e` in the box, is the absorbed star set's nominal point at the factors
`(α, e)`: the lifted predicate reads the old factors only, the new ones lie in the error box
appended to the coefficient box, and the new identity generators add `e` to the point.

## Inputs
* `s` – float star set

## Hypotheses
* none

## Conclusion
* the set lies in the nominal part of the absorbed star set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float.SoundFloatArithmetic Float.FloatOps InflatedContSet Pointwise

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of the set, box included, is a nominal point of `absorbRounding`. -/
theorem StarSet.absorbRounding_nominal (s : StarSet 𝕋 n) : -- --- CONCL ---
    s.construct ⊆ nominalSet s.absorbRounding := by -- --- PROOF ---
  -- a point is a nominal point plus an error within the box
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨α, ⟨hbox, hP⟩, hy⟩ := StarSet.mem_nominalSet_iff s y |>.mp hy
  -- the witness: the old factors, which meet the old predicate, then the error, in its box
  have hA : (fun k => (Fin.append α e : Vec ℝ (s.m + n)) (Fin.castAdd n k)) = α :=
    funext fun k => Fin.append_left α e k
  have hB : (fun k => (Fin.append α e : Vec ℝ (s.m + n)) (Fin.natAdd s.m k)) = e :=
    funext fun k => Fin.append_right α e k
  refine (StarSet.mem_nominalSet_iff _ _).mpr
    ⟨Fin.append α e, ⟨(Interval.mem_append_iff s.dom s.I_error _).mpr ⟨?_, ?_⟩,
      (HPolytope.mem_lift_nominal_iff s.pred (Fin.castAdd_injective s.m n)).mpr ?_⟩, fun i => ?_⟩
  · exact (congrArg (· ∈ s.dom.construct) hA).mpr hbox
  · exact (congrArg (· ∈ s.I_error.construct) hB).mpr he
  · exact (congrArg (· ∈ s.pred.nominal.construct) hA).mpr hP
  -- the point: the identity generators add the error
  · have hunit : ∀ k : Fin n, toReal (if k = i then (one : 𝕋) else zero) = if k = i then 1 else 0 :=
      fun k => by split_ifs <;> simp [toReal_one, toReal_zero]
    show y i + e i = toReal (s.c i) + ∑ k : Fin (s.m + n),
      toReal (Fin.append (s.G i) (fun k : Fin n => if k = i then (one : 𝕋) else zero) k)
        * (Fin.append α e : Fin (s.m + n) → ℝ) k
    rw [Fin.sum_univ_add, hy i]
    simp [Fin.append_left, Fin.append_right, hunit, add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
