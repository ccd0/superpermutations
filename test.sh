#!/bin/bash
cd "$(dirname "${BASH_SOURCE[0]}")" || exit
coqc ListTheorems.v
coqc NumPermutations.v
coqc Bounds.v
coqtop < test.v
