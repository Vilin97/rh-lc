module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleBundlesDescendFgSubfieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexSymmetricAmpleSquareDecompositionStatement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFiniteExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtension

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianAmpleSymmPreservedFieldBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.FieldBaseChange

theorem inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

theorem abelian_ample_symm_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  intro k Ω _ _ σ A₀ _ hA L hL hamp hsym
  have h := isGrpPullback_pullback A₀ (spMap σ)
  refine ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h, ?_, ?_⟩
  · have := hA.proper
    exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp h.1
  · have hinv := inv_left_comp h
    have i₁ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (pullback.fst A₀.hom (spMap σ))
      (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left _ rfl
    have i₂ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (GrpObj.inv : A₀ ⟶ A₀).left
      (pullback.fst A₀.hom (spMap σ)) _ hinv.symm
    have i₃ := GlobalTheory.RigidBundleGlue.LBIso.pull hsym (pullback.fst A₀.hom (spMap σ))
    exact (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      i₁.symm i₂).trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) i₃

end GlobalTheory.FieldBaseChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianAmpleSymmPreservedFieldBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.abelian_ample_symm_preserved_field_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  first | exact @GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange | exact GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange | (intros; apply GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompatibleEmbedding

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

open scoped TensorProduct

namespace GlobalTheory

theorem exists_finite_ext_compat_of_finite :
    ∀ (k K k₁ : Type) [Field k] [Field K] [Field k₁] [Algebra k K] [Algebra k k₁] [FiniteDimensional k k₁], ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (e : k₁ →+* K'), e.comp (algebraMap k k₁) = (algebraMap K K').comp (algebraMap k K) := by
  intro k K k₁ _ _ _ _ _ _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] k₁)
  letI : Field ((K ⊗[k] k₁) ⧸ m) := Ideal.Quotient.field m
  have hfin : FiniteDimensional K ((K ⊗[k] k₁) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  refine ⟨(K ⊗[k] k₁) ⧸ m, inferInstance, inferInstance, hfin,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : k₁ →ₐ[k] K ⊗[k] k₁).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [IsScalarTower.algebraMap_apply K (K ⊗[k] k₁) ((K ⊗[k] k₁) ⧸ m),
    Algebra.TensorProduct.algebraMap_apply]
  congr 1
  rw [← Algebra.TensorProduct.algebraMap_apply', ← Algebra.TensorProduct.algebraMap_apply]
  exact IsScalarTower.algebraMap_apply k K (K ⊗[k] k₁) a

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompatibleEmbeddingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_finite_extension_compatible_embedding : ∀ (k K k₁ : Type) [Field k] [Field K] [Field k₁] [Algebra k K] [Algebra k k₁] [FiniteDimensional k k₁], ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (e : k₁ →+* K'), e.comp (algebraMap k k₁) = (algebraMap K K').comp (algebraMap k K) := by
  first | exact @GlobalTheory.exists_finite_ext_compat_of_finite | exact GlobalTheory.exists_finite_ext_compat_of_finite | (intros; apply GlobalTheory.exists_finite_ext_compat_of_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFgStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.nonempty_ringHom_complex_of_fg' : ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  first | exact @GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg | exact GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg | (intros; apply GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.transport_power_decomposition_field_extension : ∀ (k K k₁ K' : Type) [Field k] [Field K] [Field k₁] [Field K'] (a : k →+* K) (b : k →+* k₁) (c : K →+* K') (d : k₁ →+* K'), c.comp a = d.comp b → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp K)) [GrpObj A] (π : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap a) π → ∀ (L₀ M₀ : LB A₀.left) (L M : LB A.left), L₀.IsLB → M₀.IsLB → L.IsLB → M.IsLB → LBIso L (L₀.pull π) → LBIso M (M₀.pull π) → SqDec ((Over.pullback (spMap b)).obj A₀) (L₀.pull (pullback.fst A₀.hom (spMap b))) (M₀.pull (pullback.fst A₀.hom (spMap b))) → SqDec ((Over.pullback (spMap c)).obj A) (L.pull (pullback.fst A.hom (spMap c))) (M.pull (pullback.fst A.hom (spMap c))) := by
  first | exact @GlobalTheory.SqDecTransport.transport | exact GlobalTheory.SqDecTransport.transport | (intros; apply GlobalTheory.SqDecTransport.transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareDecompositionFiniteExtensionAmpleBun

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem sqDec_of_finite_extension : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  intro K _ _ A _ hA L M hL hM aL aM sL sM
  obtain ⟨k₀, A₀, _, π, L₀, M₀, hfg, hA₀, hπ, hL₀, hM₀, aL₀, aM₀, sL₀, sM₀, eL, eM⟩ :=
    GlobalTheory.T.abelianVariety_ampleBundles_descend_fg_subfield K A hA L M hL hM aL aM sL sM
  obtain ⟨σ⟩ := GlobalTheory.T.nonempty_ringHom_complex_of_fg' K k₀ hfg
  obtain ⟨hC, aLC, sLC⟩ := GlobalTheory.T.abelian_ample_symm_preserved_field_baseChange k₀ ℂ σ A₀ hA₀ L₀ hL₀ aL₀ sL₀
  obtain ⟨-, aMC, sMC⟩ := GlobalTheory.T.abelian_ample_symm_preserved_field_baseChange k₀ ℂ σ A₀ hA₀ M₀ hM₀ aM₀ sM₀
  have hsq := GlobalTheory.T.complex_symmetricAmple_square_decomposition ((Over.pullback (spMap σ)).obj A₀) hC _ _ (pull_isLB hL₀ _) (pull_isLB hM₀ _) aLC aMC sLC sMC
  obtain ⟨k₁, _, _, _, hsq₁⟩ := GlobalTheory.T.squareDecomposition_descends_to_finiteExtension k₀ ℂ σ A₀ hA₀ L₀ M₀ hL₀ hM₀ hsq
  obtain ⟨K', _, _, _, e, he⟩ := GlobalTheory.T.exists_finite_extension_compatible_embedding k₀ K k₁
  exact ⟨K', inferInstance, inferInstance, inferInstance,
    GlobalTheory.T.transport_power_decomposition_field_extension k₀ K k₁ K' (algebraMap k₀ K) (algebraMap k₀ k₁) (algebraMap K K') e he.symm A₀ A π hπ L₀ M₀ L M hL₀ hM₀ hL hM eL eM hsq₁⟩

end GlobalTheory.SqDecFinite
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareDecompositionFiniteExtensionAmpleBunStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  first | exact @GlobalTheory.SqDecFinite.sqDec_of_finite_extension | exact GlobalTheory.SqDecFinite.sqDec_of_finite_extension | (intros; apply GlobalTheory.SqDecFinite.sqDec_of_finite_extension <;> assumption)
end
end
