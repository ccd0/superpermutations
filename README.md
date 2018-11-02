Work in progress on converting known results on the [minimal superpermutation problem](https://oeis.org/A180632) into computer-verifiable proofs checkable with [Coq](https://coq.inria.fr/).
Main results proven so far are in Bounds.v.

Tested in Coq 8.5.0 through 8.8.2. May require changes to work in future versions.

ListTheorems.v and NumPermutations.v must be compiled for the results in Bounds.v to go through:

    coqc ListTheorems.v
    coqc NumPermutations.v
