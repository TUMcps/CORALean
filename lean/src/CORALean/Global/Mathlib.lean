import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# The Mathlib surface CORALean uses

Mathlib enters the project here and nowhere else, narrowly rather than
wholesale: importing all of it makes every file depend on every file in Mathlib.
Each import is load-bearing; adding a lemma may mean adding one.
-/
