module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

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
