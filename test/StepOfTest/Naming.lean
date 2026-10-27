module

public import CORALean.Global.StepOf

/-! The naming rules: `aux_` is `private`, `step_` carries `@[step_of]`, and `@[step_of]` is only
for a public `step_` declaration. -/

@[expose] public section

namespace StepOfTest

private def aux_ok (n : Nat) : Nat := n

@[step_of ok] def step_ok (n : Nat) : Nat := n

/--
error: `StepOfTest.aux_public` is named `aux_…`, so it is `private`; a public step is named `step_…` and carries `@[step_of …]` (#269)
-/
#guard_msgs in
def aux_public (n : Nat) : Nat := n

/--
error: `StepOfTest.step_bare` is named `step_…` but carries no `@[step_of X]` naming its algorithm (#269)
-/
#guard_msgs in
def step_bare (n : Nat) : Nat := n

/--
error: `@[step_of]` is for a declaration named `step_…`, not `StepOfTest.helper` (#269)
-/
#guard_msgs in
@[step_of ok] def helper (n : Nat) : Nat := n

/--
error: `_private.StepOfTest.Naming.0.StepOfTest.step_hidden` is named `step_…`, so it is public; a `private` helper is named `aux_…` (#269)
-/
#guard_msgs in
@[step_of ok] private def step_hidden (n : Nat) : Nat := n

end StepOfTest
