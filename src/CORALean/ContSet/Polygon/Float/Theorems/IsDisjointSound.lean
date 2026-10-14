module

public import CORALean.ContSet.Polygon.Float.Operations.IsDisjoint
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# A `true` from `Polygon.isDisjoint` proves the regions disjoint

A common point lies in a piece of each polygon; the separating direction of that pair bounds
`d · x` above by the first piece's bound and below by the negated bound of the second along
`-d`, and the certified gap between the two is a contradiction.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isDisjoint_sound {P Q : Polygon 𝕋} (h : Polygon.isDisjoint P Q = true) :
    Disjoint (ContSet.construct P) (ContSet.construct Q) := by -- --- PROOF ---
  simp only [Polygon.isDisjoint, List.all_eq_true, List.any_eq_true] at h
  rw [Set.disjoint_left]
  intro x hP hQ
  obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hP
  obtain ⟨q, hq, hxq⟩ := SetUnion.mem_construct.mp hQ
  obtain ⟨d, -, hd⟩ := h p hp q hq
  -- the two bounds along `d` and `-d`, at the common point
  have h₁ := (p.boundDot (c := rowLin (fun _ : Fin 1 => d) 0) d fun _ => rfl).le x hxp
  have h₂ := (q.boundDot (c := rowLin (fun _ : Fin 1 => fun j => neg (d j)) 0)
    (fun j => neg (d j)) fun _ => rfl).le x hxq
  have hgap := toReal_lt_of_ltStrict hd
  rw [toReal_neg] at hgap
  -- the functional along `-d` is the negation of the one along `d`
  have hneg : (rowLin (fun _ : Fin 1 => fun j => neg (d j)) 0) x
      = -(rowLin (fun _ : Fin 1 => d) 0) x := by
    simp [rowLin, Real.HPolytope.rowLin, Matrix.mulVec, dotProduct, toRealMat, toReal_neg]
  rw [hneg] at h₂
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
