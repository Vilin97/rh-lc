import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrystallineSemistableComparison
import GroundTheory.PAdicHodge.BCrisNewtonLift
import GroundTheory.PAdicHodge.AInfGalois
import GroundTheory.PAdicHodge.AInfXi
import GroundTheory.PAdicHodge.TiltAlgClosed
import GroundTheory.PAdicHodge.TiltAlgebra
import GroundTheory.PAdicHodge.TateCpTwist
import GroundTheory.PAdicHodge.ExtRobbaBounded
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PAdicHodge.SemilinearResidue
import GroundTheory.PAdicHodge.SlopeRobbaDegree
import GroundTheory.PAdicHodge.BCrisEigenWitt
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.ACrisBdR
import GroundTheory.PAdicHodge.BdRGalois
import GroundTheory.PAdicHodge.ACrisBdRGalois
import GroundTheory.PAdicHodge.InstMulSemiringActionGalPlus
import GroundTheory.PAdicHodge.BCrisNewtonApprox
import GroundTheory.PAdicHodge.UnramifiedFrob
import GroundTheory.PAdicHodge.BdRTGalois
import GroundTheory.PAdicHodge.BCrisPlusInvariants
import GroundTheory.PAdicHodge.BCrisRegularFinal
import GroundTheory.PAdicHodge.ACrisGalois
import GroundTheory.PAdicHodge.FundamentalSeqSurj
import GroundTheory.PAdicHodge.FontaineLemmaInvariants
import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite
import GroundTheory.PAdicHodge.BCrisNewton

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (l) in

abbrev Fr : Subfield (BdR l) :=
  ACris.fracBCris (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one

end CrystallineSemistableComparison
