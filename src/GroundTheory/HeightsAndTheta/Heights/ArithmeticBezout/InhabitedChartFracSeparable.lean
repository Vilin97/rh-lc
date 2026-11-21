import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealBelow
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocDomain
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartKernel
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncDomain
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial LineChowForm SectionLine

noncomputable section

namespace ChartFracSeparableInhabited

theorem chartLocDomain : ChartLocDomain.Statement :=
  ChartLocDomain.proof (IncIdealBelow.proof ChowFormMultiHomog.full) ChartIncDomain.proof
    (ChartKernel.proof IncidenceGeneric.full ChartIncDomain.proof)

set_option synthInstance.maxHeartbeats 400000 in

end ChartFracSeparableInhabited

open ChartFracSeparableInhabited in

set_option synthInstance.maxHeartbeats 400000 in
open ChartFracSeparableInhabited in

end

end GroundTheory.Heights₂.Heights
