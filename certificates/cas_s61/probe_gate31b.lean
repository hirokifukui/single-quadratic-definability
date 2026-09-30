import ResearchUpgrade
open DiophCompression.ResearchUpgrade
-- s61 GATE31 probe b: floorThird on negative inputs is the floor (GPT A §3.3 "負の入力も整数Euclid除法").
-- Expected: -1 -1 -1 -2 0 0 0 1 ; PLANT line must print false.
#eval [(-1 : ℤ), -2, -3, -4, 0, 1, 2, 3].map (fun t => floorThird (fun _ => t) 0)
#eval ([(-1 : ℤ), -2, -3, -4, 0, 1, 2, 3].map (fun t => floorThird (fun _ => t) 0)) == [-1, -1, -1, -2, 0, 0, 0, 1]
#eval IO.println "@@SEP@@ PLANT (T-division values claimed; must be false)"
#eval ([(-1 : ℤ), -2, -3, -4].map (fun t => floorThird (fun _ => t) 0)) == [0, 0, -1, -1]
