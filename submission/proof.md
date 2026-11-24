# A pinned NP verifier for encoded disjunction pairs

For any Boolean-word language G in the pinned NP class, the exact theorem supplies another pinned NP language H. A canonical encoding of x and y belongs to H if and only if at least one of x and y belongs to G. The statement gives the canonical encoding explicitly as a unary delimiter prefix, the first word, and the second word. The construction also supplies precise semantics on arbitrary raw inputs by applying the reference pair parser and taking the disjunction of the memberships of the decoded words.

Use the relation and polynomial from the given NP witness for G. A certificate for H consists of a leading tag followed by a certificate for the chosen component. The machine extracts both components of the query word and uses the leading certificate bit to select one of them. It then tests the original verifier relation on the selected component and the certificate tail. The guard checks the original polynomial length bound at the length of the component, in addition to the outer witness bound at the full query length. The leading-bit read, selected input extraction, and certificate tail operate as measured primitives, with the original relation decider composed through the pinned normal-form interface.

For a YES input under either branch, the proof obtains a bounded witness from the original NP relation and prepends the appropriate tag. The machine's checked selection law returns the intended component. The outer certificate bound is one plus the original polynomial evaluated at the encoded query length. The chosen component has length at most the raw query length, and monotonicity of a polynomial over natural coefficients transfers the original witness bound. Adding one for the branch tag gives an explicit length bound on a canonical accepting certificate. Empty original witnesses pose no special issue because each receives a one-bit tag.

Conversely, any accepted witness supplies a selected decoded component and a tail satisfying the original guard and relation. This yields membership of the selected component in G. The proof works on all raw certificate words. The leading-bit primitive uses a default false for an empty certificate, so an accepted empty certificate still represents an actual empty witness for the first branch and cannot make a NO pair pass. There is no need to reject unused encoding variants for this existential language equivalence.

The result lets any NP-hardness assumption be applied to the paired disjunction of two verifier-prefix extension problems. A polynomial-time reduction from the resulting H then gives the measured image needed for sparse collision pruning. That application does not need an NP reduction to preserve witness counts because only disjunctive membership drives the pruning. The present theorem proves the disjunction closure and its exact encoding and certificate facts. Sparsity hypotheses and deterministic collapse results belong to the subsequent use of the lemma.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
