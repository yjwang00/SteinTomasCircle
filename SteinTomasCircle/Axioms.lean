import SteinTomasCircle.MainTheorems

/-!
# Axiom check

Building this file prints the axioms used by each main theorem. The expected output is
`[propext, Classical.choice, Quot.sound]` for every theorem (in particular, no `sorryAx`).
-/

#print axioms SteinTomasCircle.theorem_1_1
#print axioms SteinTomasCircle.theorem_1_1_constants
#print axioms SteinTomasCircle.theorem_1_1_maximizer
#print axioms SteinTomasCircle.theorem_1_2
#print axioms SteinTomasCircle.theorem_1_2_optimal
