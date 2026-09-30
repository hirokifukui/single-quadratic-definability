/-
  QuadraticThreeWitnessCore.lean — r11 (GPT r10 必須C): the minimal root for the two main
  r = 3 theorems. Importing this single module builds exactly the dependency closure needed for
  `graphCapacityZ_three_two` and `graphAchievableZ_three_two_iff`, and the two #print axioms
  lines below expose their footprints. The measured closure lives in
  manuscript/DEPENDENCY_CLOSURE_3W.md; the build log in certificates/minimal_3w_build.log.
-/
import DiophCompression.SemanticQuadraticSingular.Assembly3W

#print axioms DiophCompression.SemanticQuadraticSingular.graphCapacityZ_three_two
#print axioms DiophCompression.SemanticQuadraticSingular.graphAchievableZ_three_two_iff
