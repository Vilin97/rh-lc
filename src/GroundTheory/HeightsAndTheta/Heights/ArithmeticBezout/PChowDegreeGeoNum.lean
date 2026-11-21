import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeClosedPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime geoNum divSupp multAt)

theorem linForm_single {F : Type} [Field F] {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : F)) = X i := by
  simp [linForm, Pi.single_apply]

end ObjectsChow

end GroundTheory.Heights₂.Heights
