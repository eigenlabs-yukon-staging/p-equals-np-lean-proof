# Isolating the witnesses of a pinned NP verifier

The theorem quantifies over arbitrary languages in the pinned
NP definition. For each language, it obtains a polynomial-time
decidable witness relation and its polynomial witness
length bound. The theorem gives a finite witness set for every
raw input. Its elements are exactly the bounded words accepted
by the relation. The input belongs to the NP language exactly
when the set is nonempty.

The witness set is defined by a finite list-word enumeration
filtered by the relation. The verification of membership
uses induction on the length cap and the explicit split of
nonempty words into their first Boolean bit and their tail.
This enumeration is used to express and prove a finite
cardinality theorem. It is not a polynomial-time enumeration
claim. The only decision procedure assertion in the theorem
is for the original relation obtained from the pinned NP
membership evidence.

For a yes-input, an injective length-and-payload encoding puts
the entire bounded witness set into a vector space of dimension
twice the witness length bound plus one. The preceding
affine hashing theorem gives an output width at most that
dimension plus two and at least a one-eighth fraction of
seeds isolating one witness in the all-zero bucket. The good
width is existential and can depend on the size of the
witness set. For an input outside the language, there are
no bounded witnesses, so no affine seed can isolate one.

This development connects finite isolation to the repository's
actual polynomial witness relations. It does not implement
a seed sampler, an encoded hash verifier, or a randomized
class containment. The supplied source and exact statements
reproduce the pinned kernel check.

The independent exact theorem PinnedNPWitnessFinset relates any
reference NP input to the finite set of accepted bounded
witnesses and bounds its cardinality plus one by two to the
power of the cap plus one. The witness universe has exactly
that many words plus one because a new length level splits
nonempty words by their first bit and also keeps the empty word.
