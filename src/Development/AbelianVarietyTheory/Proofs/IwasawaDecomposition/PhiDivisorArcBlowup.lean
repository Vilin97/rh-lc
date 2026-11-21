module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePartStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem idlAlong_comap {X X' : Scheme.{0}} (k : X' ⟶ X) (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X') : idlAlong (I.comap k) ξ = idlAlong I (ξ ≫ k) := by
  unfold idlAlong
  rw [VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

theorem idlAlong_pow {X : Scheme.{0}} (I : X.IdealSheafData) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) : idlAlong (I ^ n) ξ = idlAlong I ξ ^ n := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  rw [TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, ← Ideal.map_pow]
  congr 1

end GlobalTheory.TorRef
