Work in progress on converting known results on the [minimal superpermutation problem](https://oeis.org/A180632) into computer-verifiable proofs checkable with [Coq](https://coq.inria.fr/).
Main results proven so far are in Bounds.v.

Last working in Coq 8.4. May require changes to work in newer versions.

ListTheorems.v and NumPermutations.v must be compiled for the results in Bounds.v to go through:

    coqc ListTheorems.v NumPermutations.v
