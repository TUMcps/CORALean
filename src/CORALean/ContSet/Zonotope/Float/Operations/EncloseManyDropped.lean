import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.encloseManyDropped`, over a floating-point scalar

The axis `encloseMany` leaves out of the standard basis: the one most aligned with the unit vector
`newGen`, the entry of largest magnitude (CORA sorts `h(i) = |newGen' e_i|` and drops `ind(end)`).
The ranking is a left fold by `le`, which certifies `≤` only, and a tie keeps the first index.
Whichever index it picks, the matrix `encloseManyBasis` is invertible as soon as `newGen` is
nonzero *there*, which is what `encloseMany` tests, so a misranking costs nothing but tightness.

Source: [1].

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index `encloseMany` leaves out of the standard basis: the entry of `newGen` of largest
magnitude. -/
def Zonotope.encloseManyDropped (newGen : Vec 𝕋 (m + 1)) : Fin (m + 1) :=
  (List.finRange (m + 1)).foldl
    (fun best k => if le (absolute (newGen k)) (absolute (newGen best)) then best else k) 0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
