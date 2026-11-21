import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerRightBlockMulBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.LevReps

theorem reps : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ F : Finset (Bridge.Gf S), (∀ u ∈ F, u ∈ B.levJ ψ) ∧
      ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  first
  | exact @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | (apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ ..)

end GlobalTheory.LevReps
end
