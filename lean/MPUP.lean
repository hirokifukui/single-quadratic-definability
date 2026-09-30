-- Root module for the `MPUP` library (frozen base, Theorem 0).
-- Added r06 (2026-08-27) so that a plain `lake build` (default target `MPUP`) succeeds
-- from a fresh clone. It imported the five frozen modules and nothing else until s32.
-- s32 (2026-09-03): MPUP.WeightedBound is imported as a sixth module. It adds the graded
-- refinement of the counting bound; the five frozen modules keep their bytes unchanged.
import MPUP.Spec
import MPUP.Gate
import MPUP.Task1
import MPUP.Obstruction
import MPUP.Quantitative
import MPUP.WeightedBound
