module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverBaseChangeComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChangeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyDescendsFieldStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveAxesDescendField

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem one_tmul_injective_field (K L M : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Function.Injective (fun m : M ↦ (1 : L) ⊗ₜ[K] m) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (fun m : M ↦ (1 : L) ⊗ₜ[K] m) = ((Algebra.linearMap K L).rTensor M) ∘ (TensorProduct.lid K M).symm := by
    funext m; simp
  rw [h2]; exact h1.comp (TensorProduct.lid K M).symm.injective

theorem pullHO_injective_field (K L : Type) [Field K] [Field L] [Algebra K L] (X X' : Scheme.{0}) (s : X ⟶ Sp K)
    (s' : X' ⟶ Sp L) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap K L))) (hs : IsSeparated s)
    (hq : QuasiCompact s) :
    Function.Injective (pullHO1 h.w) ∧ Function.Injective (pullHO2 h.w) := by
  obtain ⟨⟨e1, he1⟩, ⟨e2, he2⟩⟩ := GlobalTheory.T.structure_cohomology_flat_base_change K L X X' s s' φ h hs hq
  refine ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩
  · apply one_tmul_injective_field K L
    apply e1.injective
    simp only [he1, hab]
  · apply one_tmul_injective_field K L
    apply e2.injective
    simp only [he2, hab]

theorem noPrimO2_axesO1_descend : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  intro K L _ _ _ A _ B _ φ hφ hA
  have hpA : IsProper A.hom := hA.proper
  have hpAA : IsProper (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨Φ, hΦ, hμ, hf, hs, ha1, ha2⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback K L (algebraMap K L) A B φ hφ
  have injA := pullHO_injective_field K L A.left B.left A.hom B.hom φ hφ.1 inferInstance inferInstance
  have injAA := pullHO_injective_field K L (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom Φ hΦ
    inferInstance inferInstance
  have N := pull_over_baseChange_comm K L (algebraMap K L)
  refine ⟨fun hB z hz ↦ ?_, fun hB y h1 h2 ↦ ?_⟩
  · apply injA.2
    rw [map_zero]
    apply hB
    have e := congrArg (pullHO2 hΦ.w) hz
    rw [map_add (f := _)] at e
    rw [← (N A (A ⊗ A) B (B ⊗ B) μ[A] μ[B] φ Φ hφ.1.w hΦ.w hμ).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (fst A A) (fst B B) φ Φ hφ.1.w hΦ.w hf).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (snd A A) (snd B B) φ Φ hφ.1.w hΦ.w hs).2]
    exact e
  · apply injAA.1
    rw [map_zero]
    apply hB
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha1).1, h1, map_zero]
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha2).1, h2, map_zero]

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveAxesDescendFieldStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.primitive_axes_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  first | exact @GlobalTheory.AbCoh.noPrimO2_axesO1_descend | exact GlobalTheory.AbCoh.noPrimO2_axesO1_descend | (intros; apply GlobalTheory.AbCoh.noPrimO2_axesO1_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1RankDescendsField

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem finrank_HO1_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K L _ _ _ A _ B _ φ hpb hA g hfin hrank
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := flat_baseChange_HO K L A.left B.left A.hom B.hom φ hpb.1 inferInstance inferInstance
  haveI : Module.Finite L (L ⊗[K] HO1 A.hom) := Module.Finite.equiv e.symm
  have hr : Module.rank L (L ⊗[K] HO1 A.hom) = Cardinal.lift (Module.rank K (HO1 A.hom)) :=
    Module.rank_baseChange
  have hfinA : Module.Finite K (HO1 A.hom) := by
    rw [← Module.rank_lt_aleph0_iff]
    have h1 : Module.rank L (L ⊗[K] HO1 A.hom) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [hr] at h1
    simpa using h1
  refine ⟨hfinA, ?_⟩
  rw [← hrank, ← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1RankDescendsFieldStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.structure_h1_rank_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  first | exact @GlobalTheory.AbCoh.finrank_HO1_descend_field | exact GlobalTheory.AbCoh.finrank_HO1_descend_field | (intros; apply GlobalTheory.AbCoh.finrank_HO1_descend_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyField

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelian_HO_field_any : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧
      Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  intro K _ A _ g hab hsm
  let L := AlgebraicClosure K
  let σ : K →+* L := algebraMap K L
  have hpb : IsPullback (pullback.fst A.hom (spMap σ)) (pullback.snd A.hom (spMap σ)) A.hom (spMap σ) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨inst, hgp, habB, hsmB⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' K L σ A _ _ _ hpb
  have hB := @GlobalTheory.T.structureSheafCohomology_abelianVariety_algClosed L _ _ (Over.mk (pullback.snd A.hom (spMap σ))) inst g (habB hab) (hsmB g hsm)
  obtain ⟨hfin, hrk, hw, hnp, hax⟩ := hB
  obtain ⟨hfinA, hrkA⟩ := @GlobalTheory.T.structure_h1_rank_descends_field K L _ _ _ A _ _ inst _ hgp hab g hfin hrk
  obtain ⟨hnpA, haxA⟩ := @GlobalTheory.T.primitive_axes_descend_field K L _ _ _ A _ _ inst _ hgp hab
  exact ⟨hfinA, hrkA, @GlobalTheory.T.wedge_property_descends_field K L _ _ _ A _ _ inst _ hgp hab hw, hnpA hnp, haxA hax⟩

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyFieldStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  first | exact @GlobalTheory.AbCoh.abelian_HO_field_any | exact GlobalTheory.AbCoh.abelian_HO_field_any | (intros; apply GlobalTheory.AbCoh.abelian_HO_field_any <;> assumption)
end
end
