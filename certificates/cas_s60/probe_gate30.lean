import ResearchUpgrade
open DiophCompression.ResearchUpgrade
-- s60 GATE30 intake probe: #check of every Lean name GPT's R48 review relies on.
-- Last two entries are planted controls: they MUST fail (unknown identifier).
#eval IO.println "@@SEP@@ TCER def"
#print TCERBridge.TernaryCosetEventualRepresentation
#eval IO.println "@@SEP@@ rn_two_roots"
#check @rn_two_roots
#eval IO.println "@@SEP@@ rn_classify"
#check @rn_classify
#eval IO.println "@@SEP@@ scalar_commonSlope_or_rn_of_TCER"
#check @scalar_commonSlope_or_rn_of_TCER
#eval IO.println "@@SEP@@ scalar_singleQuadratic_iff_of_TCER"
#check @scalar_singleQuadratic_iff_of_TCER
#eval IO.println "@@SEP@@ singleQuadratic_iff_commonSlope_of_TCER_of_ne_one"
#check @singleQuadratic_iff_commonSlope_of_TCER_of_ne_one
#eval IO.println "@@SEP@@ commonSlopeIntNF_of_zero_outputs"
#check @commonSlopeIntNF_of_zero_outputs
#eval IO.println "@@SEP@@ zeroWitness_of_globalQuadratic"
#check @zeroWitness_of_globalQuadratic
#eval IO.println "@@SEP@@ zeroWitness_of_parityAffine"
#check @zeroWitness_of_parityAffine
#eval IO.println "@@SEP@@ singleQuadratic_of_scalarFamilies"
#check @singleQuadratic_of_scalarFamilies
#eval IO.println "@@SEP@@ sealed_scalarFamilies_of_TCER"
#check @sealed_scalarFamilies_of_TCER
#eval IO.println "@@SEP@@ commonSlope_of_TCER_of_two_le_polarRank"
#check @commonSlope_of_TCER_of_two_le_polarRank
#eval IO.println "@@SEP@@ singleQuadratic_padZero_iff_of_TCER"
#check @singleQuadratic_padZero_iff_of_TCER
#eval IO.println "@@SEP@@ commonSlope_comp"
#check @commonSlope_comp
#eval IO.println "@@SEP@@ commonSlope_posDef_presentation"
#check @commonSlope_posDef_presentation
#eval IO.println "@@SEP@@ CommonSlopeIntNF"
#print CommonSlopeIntNF
#eval IO.println "@@SEP@@ GlobalQuadratic"
#print GlobalQuadratic
#eval IO.println "@@SEP@@ ParityAffineNF"
#print ParityAffineNF
#eval IO.println "@@SEP@@ Rn"
#print Rn
#eval IO.println "@@SEP@@ sameParity_not_function"
#check @sameParity_not_function
#eval IO.println "@@SEP@@ modThree_not_total"
#check @modThree_not_total
#eval IO.println "@@SEP@@ parityFn_parityAffine"
#check @parityFn_parityAffine
#eval IO.println "@@SEP@@ affine_eq_of_eq_on_coset"
#check @affine_eq_of_eq_on_coset
#eval IO.println "@@SEP@@ PLANT_1 (must fail)"
#check @rn_two_roots_PLANTED_s60
#eval IO.println "@@SEP@@ PLANT_2 (must fail)"
#check @zeroWitness_of_commonSlope
