The new target supplies an explicit eleven-clause formula on seven variables. All clauses have exactly three distinct names. Variable zero is the terminal and occurs four times in the gadget. Variable two also occurs four times, while each of the five other names occurs five times. The all-false assignment satisfies the formula, and every satisfying assignment gives false to each of the seven variables. Names outside zero through six are unused. This is a unique model on the formula's actual variables, and it is independent of choices for names outside the formula.

The gadget was found by a finite Boolean constraint search. For each possible triple of distinct variables and each sign pattern satisfied by the all-false assignment, a Boolean selector represents whether to include that clause. Constrain the total selected incidences at every variable to its permitted cap, with a lower cap at the terminal so it can later occupy one additional position. For every nonzero assignment mask, require some selected clause that rejects that mask. The solver output is only a source of the explicit formula. Its claims and search logs are not used as premises of the Lean theorem.

In Lean, the formula is a literal list of true and false signs in the pinned clause representation. The exact clause shape, supported name range, and occurrence counts are decided on this concrete list. To verify uniqueness, restrict an arbitrary assignment to Fin 7, and use a kernel-computed proposition testing the formula for every Boolean function on those seven indices. The restriction theorem unfolds the literal, clause and CNF evaluators on the displayed clauses, and checks that their values only depend on indices below seven. The enumeration checks that every satisfying finite assignment gives false at every index. The proof uses ordinary Lean decide with a larger recursion and heartbeat allowance for finite enumeration.

Each copy can be translated onto a group of seven fresh names. Adding the terminal as one new positive literal to a short clause makes that new literal false under every satisfying extension and raises the terminal degree from four to five. A negative terminal may also supply a guaranteed true literal when preserving the support of a tautological source clause. Since the local filling assignment is unique, this gadget supplies the missing semantic ingredient for a model-preserving padding construction. The gadget theorem itself does not implement the measured padding transducer or its global fresh-name accounting. The search at smaller finite sizes and timeout cases is not used to claim optimality. The submission is a finite supporting result at the inclusion rung.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
