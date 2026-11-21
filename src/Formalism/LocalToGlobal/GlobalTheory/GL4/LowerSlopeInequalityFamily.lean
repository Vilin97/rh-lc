import Formalism.LocalToGlobal.GlobalTheory.GL4.ColumnLatticeExactSlope
import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SuccessiveMinima.StatementMink
import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover
import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordH

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem column_exact_slope_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : fam0 Fm ColSlopeEq :=
  ⟨0, fun _ _ _ _ => column_lattice_exact_slope _⟩

theorem lower_slope_inequality_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySlopeLowerOpenPart Fm :=
  familySlopeLowerOpen_of_std standard_slope_lower hook_length_bound Fm (column_exact_slope_family Fm)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
