module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosureThetaRatiosOfIsCl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftSemiabelianExtensionModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberThroughPointOfModelAboveStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberBaseChangeInjectiveLocalCompleteNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberLatticesIsoOfSpecialisingClosedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelFibreSpecializationChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMemberStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_completeDVR_local_embedding_normal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j := by
  first | exact @GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | exact GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | (intros; apply GlobalTheory.CompleteNormalDvr.exists_dvr_isCN <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianExtensionModelAboveThetaSetup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

theorem GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i),
    ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY := by
  intro g n F W Z i X₁
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver X₁.projM
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  exact ⟨Y, q, U₀, EE, ⟨G⟩, hO, hE, hq, hqp⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianExtensionModelAboveThetaSetupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_semiabelianExtensionModel_above_thetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY := by
  first | exact @GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove | exact GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove | (intros; apply GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftSemiabelianExtensionModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_trait_lift_semiabelianExtensionModel : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  first | exact @GlobalTheory.Poinc.Sep.TraitLift.exists_lift | exact GlobalTheory.Poinc.Sep.TraitLift.exists_lift | (intros; apply GlobalTheory.Poinc.Sep.TraitLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberBaseChangeInjectiveLocalCompleteNormalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.member_baseChange_injective_local_complete_normal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (j : V →+* V'), IsCN V' → Function.Injective j → IsLocalHom j → ∃ (m' : ℕ) (t' : Fin m' → V') (δ' : Fin m' → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V' (j.comp ev) X t' δ'), ∀ a mu, 𝔪.YY a mu → 𝔫.YY a mu := by
  first | exact @GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange | exact GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange | (intros; apply GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberLatticesIsoOfSpecialisingClosedPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₀) (𝔫₁ : UMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ X) (𝔫₂ : UMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → Cmp.LatTo 𝔫₁ 𝔫₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes | exact GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes | (intros; apply GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelFibreSpecializationChainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.semiabelianModel_fibre_specialization_chain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  first | exact @GlobalTheory.SpecChain.fibre_chain | exact GlobalTheory.SpecChain.fibre_chain | (intros; apply GlobalTheory.SpecChain.fibre_chain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeEquivTwoMembersSamePoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp

section Glue

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem LatTo.symm' {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    {𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪 : UMem X₁ z₁ act V ev X t δ} (h : LatTo 𝔪₀ 𝔪) : LatTo 𝔪 𝔪₀ := by
  obtain ⟨K, hK, hl⟩ := h
  have y₀ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V₀ ev₀ X₀ m₀ t₀ δ₀ 𝔪₀
  have y₁ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  refine ⟨K.symm, fun a mu => K.injective ?_, fun a mu' h => ?_⟩
  · rw [K.apply_symm_apply, hK]
    simp only [K.apply_symm_apply]
  · obtain ⟨mu, hmu⟩ := y₀.1 a
    have hc := (y₁.2.2.1 a (K mu) mu' (hl a mu hmu)).1 h
    refine (y₀.2.2.1 a mu (K.symm mu') hmu).2 fun v => ?_
    choose w hw using hc
    have e : mu' = K mu + (X₁.S.r * X₁.S.N) • w := funext fun u => by simpa using hw u
    refine ⟨K.symm w v, ?_⟩
    have e' : K.symm mu' = mu + (X₁.S.r * X₁.S.N) • K.symm w := by
      rw [e, map_add (f := _), K.symm_apply_apply, map_nsmul]
    exact congrFun e' v

theorem closed_over {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    [IsLocalHom ev] {Y : Scheme.{0}} {πY : Y ⟶ X₁.M.Z} {ξ : Sp V ⟶ Y}
    (h : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) : πY (ξ (closedPoint V)) = z₁ := by
  change (ξ ≫ πY) (closedPoint V) = z₁
  rw [h]
  change X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
  rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
  exact Scheme.fromSpecStalk_closedPoint

end Glue

section Main

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem latTo_all (hact : IsAct X₁ act)
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (𝔪 : UMem X₁ z₁ act V ev X t δ) : LatTo 𝔪₀ 𝔪 := by
  obtain ⟨Y, πY, hY⟩ := GlobalTheory.T.exists_semiabelianExtensionModel_above_thetaSetup g n F W Z i X₁
  have lift : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
      {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
      (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
        (_ : IsDiscreteValuationRing V') (ev' : X₁.M.Z.presheaf.stalk z₁ →+* V') (m' : ℕ) (t' : Fin m' → V')
        (δ' : Fin m' → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V' ev' X t' δ') (ξ : Sp V' ⟶ Y.Z),
        ξ ≫ πY = spMap ev' ≫ X₁.M.Z.fromSpecStalk z₁ ∧ LatTo 𝔪 𝔫 := by
    intro V _ _ _ ev X _ m t δ 𝔪
    obtain ⟨V₁, _, _, _, _, j₁, hcn₁, hj₁, hl₁⟩ := GlobalTheory.T.exists_completeDVR_local_embedding_normal V 𝔪.cn
    haveI := 𝔪.loc
    haveI := hl₁
    obtain ⟨V₂, _, _, _, _, j₂, ξ, hcn₂, hj₂, hl₂, hξ⟩ :=
      GlobalTheory.T.exists_trait_lift_semiabelianExtensionModel g n F W Z i X₁ z₁ Y πY hY V₁ (j₁.comp ev) inferInstance hcn₁
    haveI := hl₂
    obtain ⟨m', t', δ', 𝔫, hyy⟩ :=
      GlobalTheory.T.member_baseChange_injective_local_complete_normal g n F W Z i X₁ z₁ act hact V ev X m t δ 𝔪 V₂ (j₂.comp j₁) hcn₂ (hj₂.comp hj₁) inferInstance
    exact ⟨V₂, inferInstance, inferInstance, inferInstance, inferInstance, (j₂.comp j₁).comp ev, m', t', δ', 𝔫, ξ, hξ,
      AddEquiv.refl _, fun _ _ => rfl, hyy⟩
  obtain ⟨W₀, _, _, _, _, e₀, n₀, s₀, d₀, 𝔫₀, ξ₀, hξ₀, a₀⟩ := lift 𝔪₀
  obtain ⟨W₁, _, _, _, _, e₁, n₁, s₁, d₁, 𝔫₁, ξ₁, hξ₁, a₁⟩ := lift 𝔪
  let P : Y.Z → Prop := fun y => ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔠 : UMem X₁ z₁ act V ev X t δ) (ξc : Sp V ⟶ Y.Z),
    ξc ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → ξc (closedPoint V) = y → LatTo 𝔫₀ 𝔠
  have step : ∀ a b : Y.Z, πY a = z₁ → πY b = z₁ → a ⤳ b → (P a ↔ P b) := by
    intro a b ha hb hab
    obtain ⟨Va, _, _, _, _, eva, Xa, _, ma, ta, δa, 𝔠a, ξa, hξa, hca⟩ :=
      GlobalTheory.T.exists_uniformised_member_through_point_of_model_above g n F W Z i X₁ z₁ act hact Y πY hY a ha
    obtain ⟨Vb, _, _, _, _, evb, Xb, _, mb, tb, δb, 𝔠b, ξb, hξb, hcb⟩ :=
      GlobalTheory.T.exists_uniformised_member_through_point_of_model_above g n F W Z i X₁ z₁ act hact Y πY hY b hb
    constructor
    · intro hP V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
      have h1 := hP Va eva Xa ma ta δa 𝔠a ξa hξa hca
      have h2 := GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints g n F W Z i X₁ z₁ act hact Y πY hY Va eva Xa ma ta δa 𝔠a ξa V ev X m t δ 𝔠 ξc hξa hξc
        (by rw [hca, hc]; exact hab)
      exact h1.trans h2
    · intro hP V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
      have h1 := hP Vb evb Xb mb tb δb 𝔠b ξb hξb hcb
      have h2 := GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints g n F W Z i X₁ z₁ act hact Y πY hY V ev X m t δ 𝔠 ξc Vb evb Xb mb tb δb 𝔠b ξb hξc hξb
        (by rw [hc, hcb]; exact hab)
      exact h1.trans h2.symm'
  have key : ∀ y y' : Y.Z, Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' → (P y ↔ P y') := by
    intro y y' h
    induction h with
    | rel a b hr => exact step a b hr.1 hr.2.1 hr.2.2
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  haveI := 𝔫₀.loc
  haveI := 𝔫₁.loc
  have c₀ : πY (ξ₀ (closedPoint W₀)) = z₁ := closed_over hξ₀
  have c₁ : πY (ξ₁ (closedPoint W₁)) = z₁ := closed_over hξ₁
  have P0 : P (ξ₀ (closedPoint W₀)) := by
    intro V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
    exact GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints g n F W Z i X₁ z₁ act hact Y πY hY W₀ e₀ X₀ n₀ s₀ d₀ 𝔫₀ ξ₀ V ev X m t δ 𝔠 ξc hξ₀ hξc
      (by rw [hc])
  have P1 := (key _ _ (GlobalTheory.T.semiabelianModel_fibre_specialization_chain g n F W Z i X₁ z₁ Y πY hY _ _ c₀ c₁)).1 P0
  exact a₀.trans ((P1 W₁ e₁ X n₁ s₁ d₁ 𝔫₁ ξ₁ hξ₁ rfl).trans a₁.symm')

end Main

theorem exists_latEquiv_of_members : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (m₀ : ℕ) (t₀ : Fin m₀ → V₀) (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ K : (Fin 8 → X₀) ≃+ (Fin 8 → X), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) ∧ ∀ a mu, 𝔪₀.YY a mu → 𝔪.YY a (K mu) := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act hact V₀ _ _ _ ev₀ X₀ _ m₀ t₀ δ₀ 𝔪₀ V _ _ _ ev X _ m t δ 𝔪
  exact latTo_all hact 𝔪₀ 𝔪

end GlobalTheory.Poinc.Sep.Cmp
end
end
end
