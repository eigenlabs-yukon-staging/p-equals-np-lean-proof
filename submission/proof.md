# Weak 2-CNF backdoors at any fixed clause width

The pinned checker accepts `SmallWeakBackdoorSATInP` and `P_subset_NP`.
For each fixed number d of branch index bits and each fixed polynomial p,
the new theorem constructs a language in reference P contained in reference
SAT. It is complete on encoded CNFs of width at most 2^d when a satisfying
assignment restricted to a variable set a leaves a residual 2-CNF and
`(2^(d+1))^a.card` is at most p(input length). The binary input is the
unmodified reference CNF encoding.

Each branch scans the actual current residual formula and finds the first
clause wider than two. A fixed-depth bit decision tree indexes its encoded
variable names. A missing position falls back to a real name. The next bit
assigns the selected name. In the completeness proof, every remaining wide
clause must contain an unassigned backdoor variable, so some branch advances
toward the satisfying backdoor. Each such step consumes d+1 bits and lowers
the corresponding finite-set difference. An exact restriction proof and
the reference KSAT 2 decider check the final residual. The time certificate
uses measured iteration and a polynomial clock for enumeration. No
universal existence of a suitable backdoor is asserted.

## Reproduce

Check out brilliant-hq/pequalnp-proofs at
`a9ad395e8fab5537a9017734c14360773f375cd8`. Install Elan and Node.js, and
run `lake exe cache get` inside the clone's `lean` directory. Run `python3 submission/check.py --overlay <reference checkout>`
to install the submitted Outside modules, including the inherited files in
the source bundle. The required upstream source files in the same bundle
are checked byte-for-byte against that pinned checkout.

Set `PEQUALNP_REFERENCE_ROOT` to the absolute reference checkout and run:

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

The original checker tests the records in `statements/`. The verdicts,
module hashes and transcript digests are in `reference-check.json`.
The Python-only hosted experiment compares submitted source and
statement hashes. It cannot reproduce the Lean check in its own image.
