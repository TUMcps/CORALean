import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The Mathlib surface CORALean uses

Mathlib enters the project here and nowhere else, narrowly rather than
wholesale: importing all of it makes every file depend on every file in Mathlib.
Each import is load-bearing; adding a lemma may mean adding one.
-/
