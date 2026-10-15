# specification/@logicSignal

CORA methods of `specification/@logicSignal/` (a class of `specification/` or `specification/signals/`; a single-file class lists its public methods, constructor included), one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** none: an abstract class with no data, whose interface (`and_`, `or_`, `at`, `set`, `not`, `until`, `combine`) the signal classes `pointSegmentSignal`, `kleeneSignal`, `fourValuedSignal` and `finiteSignal` implement, each in its own table.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and` | out-of-scope | n/a — matlab-runtime | operator wrapper: `obj.and_(obj,other)`, a call of the static `and_` of the subclass; the two-signal `and_` rows of `pointSegmentSignal`, `kleeneSignal`, `fourValuedSignal` and `finiteSignal` are its content |
| `and_` | out-of-scope | n/a — matlab-runtime | abstract method declaration (`logicSignal` is an `Abstract` class: no body, only the interface its subclasses implement); the subclasses' `and_` rows carry the content |
| `at` | out-of-scope | n/a — matlab-runtime | abstract method declaration (`logicSignal` is an `Abstract` class: no body, only the interface its subclasses implement); the subclasses' `at` rows carry the content |
| `combine` | out-of-scope | n/a — matlab-runtime | abstract method declaration (`logicSignal` is an `Abstract` class: no body, only the interface its subclasses implement); the subclasses' `combine` rows carry the content |
| `not` | out-of-scope | n/a — matlab-runtime | abstract method declaration (`logicSignal` is an `Abstract` class: no body, only the interface its subclasses implement); the subclasses' `not` rows carry the content |
| `or` | out-of-scope | n/a — matlab-runtime | operator wrapper: `obj.or_(obj,other)`, a call of the static `or_` of the subclass; the two-signal `or_` rows of `pointSegmentSignal`, `kleeneSignal`, `fourValuedSignal` and `finiteSignal` are its content |
| `or_` | out-of-scope | n/a — matlab-runtime | abstract method declaration (`logicSignal` is an `Abstract` class: no body, only the interface its subclasses implement); the subclasses' `or_` rows carry the content |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `set` | out-of-scope | n/a — matlab-runtime | abstract method declaration (`logicSignal` is an `Abstract` class: no body, only the interface its subclasses implement); the subclasses' `set` rows carry the content |
| `until` | out-of-scope | n/a — matlab-runtime | abstract method declaration (`logicSignal` is an `Abstract` class: no body, only the interface its subclasses implement); the subclasses' `until` rows carry the content |
