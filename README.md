# Polymorphisms

This project contains a formalization of my paper [Aggregation of evaluations without unanimity](https://yuvalfilmus.cs.technion.ac.il/publications/papers/?id=1742).

The main definitions and results are spread across several files:

- The basic definitions are found in `Basic.lean`.
- Theorem 1.3 is found in `ReductionTo2.lean` under the name `trivial_iff_trivial_for_2`.
- Theorem 1.4 is found in `ReductionTo1.lean` under the name `trivial_for_2_of_trivial_for_1`.
- The *furthermore* clause of Theorem 1.4 is found in `BooleanAux.lean` under the name `not_trivial_for_1B`.
- The basic definitions of symmetric Boolean predicates are found in `SymmetricDefs.lean`.
- Theorem 1.5 is found in `Symmetric.lean` under the name `symmetric_classification`.
- The *furthermore* clause of Theorem 1.5 is found in `SymmetricOnlyIf.lean` under the name `nontrivial_if_has_nonconst_counterexample'`.
- The polymorphisms of NAE are determined in `NAE.lean`, specifically `NAE_polymorphisms`.
- Theorem 1.6(1) is found in `SymmetricClassify.lean` under the name `odd2_polymorphisms`.
- Theorem 1.6(2) is found in `SymmetricClassify.lean` under the name `equal_polymorphisms`.
- Theorem 1.6(3) is found in `SymmetricClassifyParity.lean` under the name `parity_polymorphisms`.
- Theorem 1.6(4) is found in `SymmetricClassifyAtmost.lean` under the name `atmost_polymorphisms`.
- Theorem 1.6(5) is found in `SymmetricClassifyAtmost_m.lean` under the name `atmost_m_polymorphisms`.
- Theorem 1.6(6) is found in `SymmetricClassification.lean` under the names `symmetric_polymorphisms_comp_closed` and `symmetric_polymorphisms_not_comp_closed`.
- Theorem 1.7 is found in `Unanimity.lean` under the name `trivial_iff_impossibility`.
