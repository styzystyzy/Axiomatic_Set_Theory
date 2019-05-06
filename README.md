# Axiomatic_Set_Theory
Axiomatic set theory is a foundational system of mathematics and has important applications in many fields. In this work, we present a formal system of axiomatic set theory based on the Coq proof assistant. The axiomatic system used in the formal system refers to Morse-Kelley set theory which is a relatively complete and concise axiomatic set theory.

In this formal system, we complete the formalization of basic definitions of sets, functions, ordinal numbers and cardinal numbers and prove the most commonly used theorems in Coq. Moreover, the non-negative integers are defined and Peano's postulates are proved as theorems. According to the axiom of choice, we also present formal proofs of Hausdorff maximal principle and Schr\"{o}eder-Bernstein theorem. The whole formalization of the system includes eight axioms, one axiom schema, 62 definitions and 148 corollaries or theorems.

The ``axiomatic set theory'' formal system is free from the more obvious paradoxes and a complete axiomatic system is constructed through it. It is designed to give quickly and naturally a foundation for mathematics. On the basis of the system, we can prove many famous theorems and quickly formalize the theories of topology, modern algebra and so on.

# Files and Modules

1. Elementary_Logic.v
  Defines notations shared by all of the other modules.
2. Classification_Axiom_Scheme.v
  Provieds a simplified and modified version of the "axiomatic set theory" formal system.
3. Elementary_Algebra.v
  Defines some notations and provides basic properties.
4. Sets_Existence.v
  Proves Tukey's lemma according to AC.
5. Ordered_Pairs.v
  Proves the Hausdorff maximal principle.
6. Functions.v
  Proves the maximal principle.
7. WellOrdering.v
  Proves Zorn's lemma on the basis of the maximal principle.
8. Ordinals.v
  Proves the well-ordering theorem.
9. NItegers.v
  Proves AC based on the well-ordering theorem.
10. Choice_Axiom.v
  Proves AC based on the well-ordering theorem.
11. Cardinal_Numbers.v
  Proves AC based on the well-ordering theorem.

# Author

Tianyu Sun. stycyj@bupt.edu.cn
