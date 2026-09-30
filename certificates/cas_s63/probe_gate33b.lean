import DiophCompression
import MPUP
-- s63 GATE33 probe b: environment of the README short build (MPUP + DiophCompression, no ResearchUpgrade).
-- Expect: DC name resolves; RU-module names are unknown (they are not in the DC import closure).
#eval IO.println "@@SEP@@ DC name (must succeed)"
#check @DiophCompression.relation_phase_diagram_all_positive_arity_of_classical
#eval IO.println "@@SEP@@ RU name sealedFullNF_of_TCER (must fail without import ResearchUpgrade)"
#check @DiophCompression.ResearchUpgrade.sealedFullNF_of_TCER
#eval IO.println "@@SEP@@ RU name generalFullNF_iff_semidefiniteFullNF (must fail)"
#check @DiophCompression.ResearchUpgrade.generalFullNF_iff_semidefiniteFullNF
