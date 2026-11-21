module

public import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem exists_cover {F : Type} [Field F] [NumberField F] (Y : Var F) {N : ℕ} (M : Fin N → GlobalTheory.TrueGeo.Model Y) :
    ∃ (V : Cover Y) (b : ∀ i, V.X ⟶ (M i).X), ∀ i, V.j ≫ b i = V.π ≫ (M i).j := by
  obtain ⟨X', π, j, hXi, hπ, hfl, H, hg⟩ := GlobalTheory.IntModel.exists_flat_model (O := 𝓞 F) Y.str Y.isProjOver
    (fun i => (M i).X) (fun i => (M i).p) (fun i => (M i).j) (fun i => (M i).ar.isProjOver) (fun i => (M i).pb.w)
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hXi, hπ, inferInstance,
    GlobalTheory.IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let M₀ : GlobalTheory.TrueGeo.Model Y := ⟨X', π, har, j, H⟩
  obtain ⟨Q, π₁, -, hQ, -, -, hj, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M₀ M₀
  choose g hg₁ _ using hg
  refine ⟨Cover.ofModel Q hQ, fun i => π₁ ≫ g i, fun i => ?_⟩
  show Q.j ≫ π₁ ≫ g i = 𝟙 _ ≫ (M i).j
  rw [← Category.assoc, hj, Category.id_comp]
  exact hg₁ i
