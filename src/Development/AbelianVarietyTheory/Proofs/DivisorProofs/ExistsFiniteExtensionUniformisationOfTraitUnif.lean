module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.SeparatedSymmetricModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOnTorusDescendsAlongLocalHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SixthLawsAndUnifUniq
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianGenericFibreTraitUniformisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTransferIsPullDegIdStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationOfTraitUniformisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem evenOn_of_unifTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  intro R _ _ _ _ D G _ _ P hG hU X _ _ _ hQ
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, -, hφ, hgp, hL, -⟩ := hU
  have hadm : AdmBase W (maximalIdeal W) := by
    haveI := hW.1
    exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap φ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)
  obtain ⟨P', hP', hE⟩ := unif_evenOn W hadm D' A' G' hG' U'
  have hpr : IsProper (pullback.snd G'.hom (jK W)) := by
    have := A'.isAb.proper
    haveI : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    change IsProper ((Over.pullback (jK W)).obj G').hom
    rw [← Over.w U'.gen.hom]
    infer_instance
  have hL' : LBIso P'.L.L (P.L.L.pull β) := by rw [hP']; exact hL
  exact GlobalTheory.T.evenOnTorus_descends_along_localHom R W φ hφ G hG G' β hgp hpr P P' hL' hE X hQ

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationOfTraitUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.evenCubicalTrivialisation_of_trait_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  first | exact @GlobalTheory.Mum.evenOn_of_unifTrait | exact GlobalTheory.Mum.evenOn_of_unifTrait | (intros; apply GlobalTheory.Mum.evenOn_of_unifTrait <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullDegTraitAndBaseUniformisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CommonPull

open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem exists_rig_iso_of_eq {S : Scheme.{0}} {H : Over S} [GrpObj H] (L₁ L₂ : RigLB H) (h : L₁ = L₂) :
    ∃ w : LB.Iso L₂.L L₁.L, w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec H) (fun _ => 1)) L₂.rig L₁.rig := by
  subst h
  exact ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso L₁.L, idIso_isGen L₁.isLB, fun p => L₁.rigGen p.1 p.2⟩

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → UnifTrait D G L →
    ∀ (D₂ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U₂ : Unif (maximalIdeal R) D₂ A G),
    U₂.LG.L = L → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (φ : R →+* W) (D' : DegPre W),
      Function.Injective φ ∧ Nonempty (IsPullDeg φ D.toPre D') ∧ Nonempty (IsPullDeg φ D₂.toPre D') := by
  intro R _ _ _ hR D G _ _ L _ hG hT D₂ A U₂ hL
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφ, hloc, hβ, hLβ, hD⟩ := hT
  subst hL
  obtain ⟨hLw, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have h6 := GlobalTheory.sixthLaws_and_unifUniq.2
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap φ))
  haveI := mbc
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)

  have sq : spMap (fracMap hφ) ≫ jK R = jK W ≫ spMap φ := (fracMap_sq hφ).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hLw.polBaseChange _ _ (spMap (fracMap hφ)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hφ)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₂.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK W)).obj G') G (spMap (fracMap hφ) ≫ jK R)
      (pullback.fst G'.hom (jK W) ≫ β) :=
    ((isGrpPullback_pullback G' (jK W)).comp hβ).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₂.gen.inv.left ≫ U₂.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₂.LG.L.pull (pullback.fst G'.hom (jK W) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₂.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₂.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₂.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₂.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₂.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · show pullback.fst G'.hom (jK W) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
      rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G := by
    show eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
    rw [hbc]; exact (cubeMapOf hβ).e_comm
  obtain ⟨wL, gwL, rwL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G G'
    (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) he U₂.LG U'.LG (by
      show ∃ w : LB.Iso U'.LG.L (U₂.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap φ))), w.IsGen
      rw [hbc]; exact hLβ)
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R (maximalIdeal R) hR.1 D₂
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) ∈ Wo := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hWo
  obtain ⟨D₂', hD₂, U₂', hLG, -, -⟩ := h4.unifBaseChange R W (maximalIdeal R) (maximalIdeal W) hR.1 hW' φ
    (map_maximalIdeal_le φ) D₂ A G hG U₂ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gwL rwL
  obtain ⟨wU, gU, rU⟩ := exists_rig_iso_of_eq U₂'.LG U'.LG hLG
  obtain ⟨hU, -⟩ := h6 W (maximalIdeal W) hW' D₂' D' A'' A' G' hG' U₂' U' wU gU rU
  obtain ⟨hD'⟩ := hD
  refine ⟨W, inferInstance, inferInstance, φ, D'.toPre, hφ, ⟨hD'⟩, ?_⟩
  exact RingHom.id_comp φ ▸ GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ Function.injective_id hD₂ hU

end GlobalTheory.Mum.CommonPull
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullDegTraitAndBaseUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_common_pullDeg_trait_and_base_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → UnifTrait D G L →
    ∀ (D₂ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U₂ : Unif (maximalIdeal R) D₂ A G),
    U₂.LG.L = L → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (φ : R →+* W) (D' : DegPre W),
      Function.Injective φ ∧ Nonempty (IsPullDeg φ D.toPre D') ∧ Nonempty (IsPullDeg φ D₂.toPre D') := by
  first | exact @GlobalTheory.Mum.CommonPull.exists_common_pull | exact GlobalTheory.Mum.CommonPull.exists_common_pull | (intros; apply GlobalTheory.Mum.CommonPull.exists_common_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.traitUniformisation_pullback_finiteExtension : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  first | exact @GlobalTheory.Mum.TraitExt.unifTrait_pull | exact GlobalTheory.Mum.TraitExt.unifTrait_pull | (intros; apply GlobalTheory.Mum.TraitExt.unifTrait_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnif

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Ident

theorem finExt_isLocalHom {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (h : FinExt ρ) : IsLocalHom ρ := by
  letI := ρ.toAlgebra
  have hm : (maximalIdeal R').comap ρ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) h.2.2.to_isIntegral (maximalIdeal R'))
  exact ((IsLocalRing.local_hom_tfae ρ).out 1 5).2 hm

theorem finExt_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsDomain R₂] [IsLocalRing R₂] {ρ : R →+* R₁} {ρ' : R₁ →+* R₂} (h : FinExt ρ) (h' : FinExt ρ') :
    FinExt (ρ'.comp ρ) :=
  ⟨h'.1, h'.2.1.comp h.2.1, h'.2.2.comp h.2.2⟩

theorem unif_along_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∀ (D₂ : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U₂ : Unif (maximalIdeal R) D₂ A G) (D₃ : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D₂.toPre D₃.toPre) →
    ∃ (G₃ : Over (Sp R')) (_ : GrpObj G₃) (_ : IsCommMonObj G₃) (β₃ : G₃.left ⟶ G.left) (A₃ : PolAV (Sp (FractionRing R')))
      (U₃ : Unif (maximalIdeal R') D₃ A₃ G₃), IsSemiAbelian G₃ ∧ IsGrpPullback G₃ G (spMap ρ) β₃ ∧
        LBIso U₃.LG.L (U₂.LG.L.pull β₃) := by
  intro R R' _ _ _ _ _ _ ρ hR hf D₂ A G _ _ hG U₂ D₃ h23
  have := hR.2
  haveI := finExt_isLocalHom hf
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hf.1 ρ hf.2.1 (map_maximalIdeal_le ρ) hG U₂
  have h3' : Nonempty (IsPullDeg (RingHom.id R') D₃.toPre D'.toPre) :=
    GlobalTheory.Mum.isPullDeg_unique_and_comp.1 R R' ρ hf.2.1 D₂.toPre D₃.toPre D'.toPre h23 ⟨hD⟩
  have hG' : IsSemiAbelian ((Over.pullback (specOf ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨U₃, hU₃, -⟩ := (GlobalTheory.T.uniformisation_transfer_isPullDeg_id R' (maximalIdeal R') hf.1 D₃ D' h3' A' _ hG').1 U'
  have hb : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (specOf ρ) := Category.id_comp _
  refine ⟨(Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ), A', U₃, hG', ?_, ?_⟩
  · exact (isGrpPullback_pullback G (spMap ρ)).congr rfl hb.symm
  · rw [hU₃]
    exact ⟨hP.lg.choose, hP.lg.choose_spec.1⟩

theorem exists_finExt_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' G (spMap φ) β → LBIso U'.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D.toPre D'.toPre) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β₁ : G₁.left ⟶ G.left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β₁ ∧ LBIso U₁.LG.L (P.L.L.pull β₁) := by
  intro R _ _ _ hR D G _ _ P hG W _ _ _ hW φ hφ hloc G' _ _ β D' A' U' hβ hL hD
  have hT : UnifTrait D G P.L.L := ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφ, hloc, hβ, hL, hD⟩
  obtain ⟨R₁, _, _, _, ρ₁, G₁, _, _, β₁, X, _, _, _, hf₁, hβ₁, hQ⟩ := GlobalTheory.Mum.exists_finExt_tq_closedFibre R hR G hG
  haveI hloc₁ : IsLocalHom ρ₁ := finExt_isLocalHom hf₁
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.MumPull.exists_pull R R₁ ρ₁ hf₁.2.1 hloc₁ D
  have hR₁ : Base R₁ := ⟨hf₁.1, by haveI := hR.2; exact charZero_of_injective_ringHom hf₁.2.1⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ₁ (isGrpPullback_pullback G (spMap ρ₁))
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback _ G hG)
  obtain ⟨P₁, w₁, hP₁L, hP₁⟩ := GlobalTheory.UU.exists_cp_pull _ _ (spMap ρ₁) G G₁ β₁ hβ₁.1.w
    (fun T x y => Over.OverMorphism.ext (hβ₁.2 T x y _ _ rfl rfl).symm) P
  have hT₁ : UnifTrait D₁ G₁ P₁.L.L := by
    rw [hP₁L]; exact GlobalTheory.T.traitUniformisation_pullback_finiteExtension R R₁ ρ₁ hR hf₁ D D₁ hD₁ G G₁ β₁ hG hβ₁ P.L.L P.L.isLB hT
  have hE : EvenOn P₁ := GlobalTheory.T.evenCubicalTrivialisation_of_trait_uniformisation R₁ hR₁ D₁ G₁ P₁ hG₁ hT₁ X hQ
  obtain ⟨A, gen, hgen, hA⟩ := GlobalTheory.T.exists_polarisedAbelian_generic_fibre_trait_uniformised R₁ hR₁ D₁ G₁ P₁ hG₁ hT₁
  obtain ⟨D₂, U₂, hU₂, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₁ hR₁ G₁ P₁ hG₁ hE A gen hgen hA
  obtain ⟨V, _, _, ψ, D', hψ, h1, h2⟩ := GlobalTheory.T.exists_common_pullDeg_trait_and_base_uniformisation R₁ hR₁ D₁ G₁ P₁.L.L P₁.L.isLB hG₁ hT₁ D₂ A U₂ (by rw [hU₂])
  obtain ⟨R', _, _, _, ρ₂, D₃, hf₂, h13, h23⟩ :=
    GlobalTheory.MumRig.exists_common_pull_finite R₁ hR₁ D₁ D₂ V ψ hψ D' h1 h2
  obtain ⟨G₃, _, _, β₃, A₃, U₃, -, hβ₃, hL₃⟩ := unif_along_finExt R₁ R' ρ₂ hR₁ hf₂ D₂ A G₁ hG₁ U₂ D₃ h23
  refine ⟨R', _, _, _, ρ₂.comp ρ₁, D₃, G₃, _, _, β₃ ≫ β₁, A₃, U₃, finExt_comp hf₁ hf₂, ?_, ?_, ?_⟩
  · obtain ⟨a⟩ := hD₁
    obtain ⟨b⟩ := h13
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hf₁.2.1 hf₂.2.1 a b
  · refine (hβ₃.comp hβ₁).congr ?_ rfl
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl
  · rw [hU₂] at hL₃
    have hPP : LBIso P₁.L.L (P.L.L.pull β₁) := ⟨w₁, hP₁.gen⟩
    exact LBIso.trans U₃.LG.isLB (LB.isLB_pull P₁.L.isLB _) (LB.isLB_pull P.L.isLB _) hL₃
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hPP β₃ rfl)

end GlobalTheory.Mum.Ident
end
end
end
