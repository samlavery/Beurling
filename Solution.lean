module

public import RequestProject.Beurling.OneZero.TheoremAprime

public section

/-!
# Proved solution

This module imports the proof development. The declarations named in `comparator.json` are
proved there under the same names as in `Challenge.lean`:

* `BModel.one_zero_system_exists` in `RequestProject/Beurling/OneZero/TheoremAprime.lean`;
* `BModel.corollary_2_2_complete` in `RequestProject/Beurling/Model/MarginComplete.lean`;
* the definitions in `RequestProject/Beurling/StatementDefs.lean`, a verbatim copy of the
  Challenge's definitions in one module.

`lake comparator` checks that each has exactly the statement (for definitions, the value) of
its counterpart in `Challenge.lean` and uses only the permitted axioms.
-/
