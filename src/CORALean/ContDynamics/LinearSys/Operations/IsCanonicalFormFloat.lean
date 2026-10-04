import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalForm
import CORALean.ContDynamics.LinearSys.Operations.EntryIsFloat

/-!
# `isCanonicalForm` at float matrices

CORA's `isCanonicalForm` [1] as a Boolean on float entries: `m = n`, `s = r`, `c`, `k`, `E`, `D`
zero and `B = I`, each entry tested by `LinearSys.entryIsFloat`. Soundness is
`LinearSys.isCanonicalFormFloat_sound`, one-sided as the test is.

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m q r s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `isCanonicalForm`, on float coefficients. -/
def LinearSys.isCanonicalFormFloat (B : Mat 𝕋 n m) (c : Vec 𝕋 n) (D : Mat 𝕋 r m) (k : Vec 𝕋 r)
    (E : Mat 𝕋 n q) (_F : Mat 𝕋 r s) : Bool :=
  (m == n) && (s == r) &&
    (List.finRange n).all (fun i => LinearSys.entryIsFloat zero (c i)) &&
    (List.finRange r).all (fun i => LinearSys.entryIsFloat zero (k i)) &&
    (List.finRange n).all (fun i => (List.finRange q).all fun j =>
      LinearSys.entryIsFloat zero (E i j)) &&
    (List.finRange r).all (fun i => (List.finRange m).all fun j =>
      LinearSys.entryIsFloat zero (D i j)) &&
    (List.finRange n).all (fun i => (List.finRange m).all fun j =>
      LinearSys.entryIsFloat (if (i : ℕ) = (j : ℕ) then one else zero) (B i j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
