import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  let s : (Out.Inh.trivLB (Sp R)).Sec :=
    ⟨fun _ => 1, fun _ _ =>
      (map_one _).trans ((congrArg₂ (· * ·) rfl (map_one _)).trans (_root_.mul_one _)).symm⟩
  have hs : ⨆ i : Fin (0 + 1), Out.nonzeroLocus ((fun _ => s) i) = ⊤ := by
    simp only [iSup_const, Out.nonzeroLocus, s, Scheme.basicOpen_one]
    exact (Out.Inh.trivLB_isLB _).cover
  have h := ProjSpace.toProj_str (𝟙 (Sp R)) (fun _ => s) hs
  refine ⟨0, _, ?_, h⟩
  have := isProper_str R 0
  have : IsClosedImmersion (ProjSpace.toProj (𝟙 (Sp R)) (fun _ => s) hs ≫ PSpace.str R 0) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ (PSpace.str R 0)

end GlobalTheory.Models.Point

end
