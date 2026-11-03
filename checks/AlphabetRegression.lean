import QuantumSep.AlgorithmicInterfaces


open QuantumSep

-- The original contradiction must no longer elaborate.
example (ptas : DenseMaxFourCSPPTASContract)
    (csp : DenseMaxFourCSP Unit Empty) (seed : ptas.Seed) : True := by
  fail_if_success have bad : Unit → Empty := ptas.solve Unit Empty csp 1 seed
  trivial

-- An empty variable set is allowed when the alphabet is inhabited.
example (ptas : DenseMaxFourCSPPTASContract)
    (csp : DenseMaxFourCSP Empty Unit) (seed : ptas.Seed) : Empty → Unit :=
  ptas.solve Empty Unit csp 1 seed

-- The same boundary applies to the wrapped randomized procedure.
example (ptas : DenseMaxFourCSPPTASContract)
    (csp : DenseMaxFourCSP Unit Empty) : True := by
  fail_if_success have bad : RandomizedProcedure Unit (Unit → Empty) :=
    ptas.procedure Unit Empty csp 1
  trivial

example (ptas : DenseMaxFourCSPPTASContract)
    (csp : DenseMaxFourCSP Empty Unit) : RandomizedProcedure Unit (Empty → Unit) :=
  ptas.procedure Empty Unit csp 1

-- Ordinary inhabited variable/alphabet instances remain accepted.
example (ptas : DenseMaxFourCSPPTASContract)
    (csp : DenseMaxFourCSP Unit Unit) (seed : ptas.Seed) : Unit → Unit :=
  ptas.solve Unit Unit csp 1 seed
