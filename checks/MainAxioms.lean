import QuantumSep

/-!
Print the kernel axiom dependencies of the two public theorem statements.
The explicit `AllowedAssumptions` parameter is a hypothesis, so its contents
are not listed by `#print axioms`. See the README for the external contracts.
-/

#print axioms QuantumSep.randomizedUnitProductOptimization_main
#print axioms QuantumSep.randomizedSeparableWeakMembership_main
