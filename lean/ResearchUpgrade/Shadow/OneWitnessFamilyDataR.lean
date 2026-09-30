/-
  Shadow/OneWitnessFamilyDataR.lean — ray-carrying shadow of the leaf certificate type.
  Every constructor of `OneWitnessFamilyData` is non-moving (kind 0 or 1), so its structured
  family lifts to a `StructuredFamilyR` for free. Verbatim transplant of
  DiophCompression/SemanticQuadratic/OneWitnessFamilyData.lean (the `toStructuredFamily` leaf).
-/
import ResearchUpgrade.Shadow.FamilyR
import DiophCompression.SemanticQuadratic.OneWitnessFamilyData

namespace DiophCompression.ResearchUpgrade

open MPUP DiophCompression.SemanticQuadratic

/-- The leaf certificate as a ray-carrying family: every constructor of `OneWitnessFamilyData`
    is non-moving, so it lifts for free. -/
def OneWitnessFamilyData.toStructuredFamilyR {A B C l m q : ℤ}
    (F : OneWitnessFamilyData A B C l m q) :
    StructuredFamilyR (fiberSet A B C l m q) :=
  StructuredFamilyR.lift F.toStructuredFamily (by
    cases F <;> simp [OneWitnessFamilyData.toStructuredFamily, StructuredFamily.kind,
      PeriodicProgression.toStructuredFamily])

end DiophCompression.ResearchUpgrade
