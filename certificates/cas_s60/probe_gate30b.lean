import ResearchUpgrade
open DiophCompression.ResearchUpgrade
#eval IO.println "@@SEP@@ c21_affine_square"
#check @c21_affine_square
#eval IO.println "@@SEP@@ deltaQ"
#print deltaQ
#eval IO.println "@@SEP@@ commonSlope_padZero_iff"
#check @commonSlope_padZero_iff
#eval IO.println "@@SEP@@ PLANT (must fail)"
#check @c21_affine_square_PLANTED_s60
