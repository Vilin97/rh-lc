module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
public import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecSep
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.InteriorEquivariantActionInvariant
public import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := open GlobalTheory.ObjPull in by
  let o : Obj D l _ (r ≫ _) :=
    have hL : LBIso t.PP.L (Y.oF.t.PP.L.pull ν.cm.F) := by
      obtain ⟨w, hw, -⟩ := ν.lin
      exact ⟨w, hw⟩
    have hpr := Y.oF.proper
    have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
      (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
      (AbelianSchemeGerms.isAbelianScheme_of_proper Y.oF.t.G Y.oF.t.semi) ν.cart hL
    { t := t
      proper := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 hpr
      ample := hp.2.1 Y.oF.ample
      ktriv := hp.2.2 Y.oF.ktriv
      eta := fun a => secPull ν.cart (Y.oF.eta a)
      eta_add := fun a c => by rw [Y.oF.eta_add, map_mul]
      eta_ker := fun a ha => by rw [Y.oF.eta_ker a ha, map_one]
      etaA := fun a => secPull ν.cart (Y.oF.etaA a)
      etaA_add := fun a c => by rw [Y.oF.etaA_add, map_mul]
      etaA_ker := fun a => by rw [Y.oF.etaA_ker a, map_one]
      geom := fun k _ _ x β hx => by
        obtain ⟨hdet, I, hI, hA, hM⟩ := Y.oF.geom k (x ≫ r) β (by rw [Category.assoc, hx])
        refine ⟨fun τ => ?_, tateMove (pushEquiv ν.cart (Over.mk x)) (fun c g => ?_) (fun n g g' u hc => ?_) I,
          hI, fun a => ?_, fun a ha => ?_⟩
        · rw [GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ,
            GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ]
          exact hdet τ
        · apply Over.OverMorphism.ext
          show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
          rw [Category.assoc, ν.act, Category.assoc]
        · exact (GlobalTheory.weilIs_grpPullback_of_comm (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
            ν.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hA a))
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hM a ha)) }
  let n : ObjMap o Y.oF r := ⟨ν, fun _ => secPull_left ν.cart _, fun _ => secPull_left ν.cart _⟩
  have sec_eq {e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G} {e' : 𝟙_ (Over S) ⟶ t.G}
      (h : e'.left ≫ ν.φ = r ≫ e.left) : e' = secPull ν.cart e := by
    apply Over.OverMorphism.ext
    apply ν.cart.1.hom_ext
    · exact h.trans (secPull_left ν.cart _).symm
    · rw [Over.w, Over.w]
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

end GlobalTheory.TransitionUnique
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorLevelActionEqRestrictionLevelMoveInv

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelMoveRestr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_frPt_ptF {K : Type} [Field K] [Algebra c.F K] (t : Sp K ⟶ Xo.XF c)
    (ht : t ≫ pullback.snd _ _ = spMap (algebraMap c.F K)) : ∃ y : FrPt Xo c K, ptF y = t := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt (Xo := Xo) (c := c) (S := K) (t ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, sOf, ← Spec.map_comp]; rfl)
  refine ⟨y, pullback.hom_ext ?_ ?_⟩
  · simp only [ptF, pullback.lift_fst]; exact hy
  · simp only [ptF, pullback.lift_snd]; exact ht.symm

theorem restr_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹ := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ γ
  haveI : IsSeparated Xo.s := Formalism.L2.Pj.sepX Xo
  haveI : IsReduced (Xo.XF c) := GlobalTheory.TransitionUnique.isReduced_XF Xo c
  refine ext_of_fromSpecResidueField_eq _ _ (pullback.snd _ _) Set.univ dense_univ (fun x _ => ?_) ?_
  · let t : Spec ((V₀ TF.Y Z).residueField x) ⟶ Sp c.F :=
      (V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z ≫ pullback.snd _ _
    letI : Algebra c.F ((V₀ TF.Y Z).residueField x) := (Spec.preimage t).hom.toAlgebra
    obtain ⟨y, hy⟩ := exists_frPt_ptF (K := (V₀ TF.Y Z).residueField x)
      ((V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z) (by
        rw [Category.assoc]
        exact (Spec.map_preimage t).symm)
    have h1 := hρ.2 γ ((V₀ TF.Y Z).residueField x) y ((V₀ TF.Y Z).fromSpecResidueField x) hy.symm
    rw [h1, GlobalTheory.CompLevelStab.ptF_move hpq hA Xo c, hy, Category.assoc]
  · have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    have h0 := hρ.1 γ
    rw [GlobalTheory.CompLevelStab.j₀_s₀, hid, Category.comp_id] at h0
    rw [Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_snd]
    exact h0

end GlobalTheory.LevelMoveRestr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorLevelActionEqRestrictionLevelMoveInvStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.interiorLevelAction_eq_restriction_levelMove_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹ := by
  first | exact @GlobalTheory.LevelMoveRestr.restr_eq | exact GlobalTheory.LevelMoveRestr.restr_eq | (intros; apply GlobalTheory.LevelMoveRestr.restr_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismIntegralMap

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

theorem exists_isGrpPullback_extend : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X' V : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → ∀ (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ] (σ : V ⟶ V) (σ' : X' ⟶ X'), σ ≫ ℓ = ℓ ≫ σ' → ∀ (G' : Over X') [GrpObj G'], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' → ∀ (A : Over V) [GrpObj A] (κ : A.left ⟶ G'.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A G' ℓ κ → ∀ ν : A.left ⟶ A.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A σ ν → ∃ M : G'.left ⟶ G'.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G' σ' M ∧ κ ≫ M = ν ≫ κ := by
  intro hext X' V _ hS ℓ _ _ σ σ' hσ G' _ hG A _ κ hκ ν hν
  have hGσ : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian ((Over.pullback σ').obj G') := IsSemiAbelian.pullback _ _ hG
  have h1 : IsGrpPullback A G' (ℓ ≫ σ') (ν ≫ κ) := (hν.comp hκ).congr hσ rfl
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor σ' ℓ h1
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  obtain ⟨e, ⟨he, he'⟩, -⟩ := hext.existsUnique_iso_of_isGrpPullback hS hG hGσ hκ h2 (Iso.refl A)
  haveI := he
  refine ⟨e.hom.left ≫ pullback.fst _ _, ?_, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' σ')).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, ← he']
    exact pullback.lift_fst _ _ _

theorem eq_of_comp_eq_of_isGrpPullback {X' V : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X']
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ]
    (G' : Over X') [GrpObj G'] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G') (A : Over V) [GrpObj A]
    (κ : A.left ⟶ G'.left) (hκ : IsGrpPullback A G' ℓ κ) (f g : G'.left ⟶ G'.left)
    (h : f ≫ G'.hom = g ≫ G'.hom) (hfg : κ ≫ f = κ ≫ g) : f = g := by
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS ℓ
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G' hG
  have : IsSchemeTheoreticallyDominant κ := .of_isPullback hκ.1.flip
  exact GlobalTheory.ExtUnique.hom_ext_of_dominant G'.hom h κ hfg

end GlobalTheory.EqvAct
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.EquivariantActionEqOfAgreeOnGenerators

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvAct
theorem equivariant_action_ext : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA1 Γ _ ι ρ hact X' _ φ ℓ ρ' hN hproj hℓ hℓφ hρ
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨n, hn, hη⟩ := _root_.GlobalTheory.T.interior_equivariant_action_invariant hP E H Dw l Xo c TF Z hpq hA Γ ι ρ (GlobalTheory.T.interiorLevelAction_eq_restriction_levelMove_inv E H Dw l Xo c TF Z hpq hA Γ ι ρ hact)
  haveI := hℓ
  haveI : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isProjOver hproj
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' := (isNormalScheme_iff_pred X').mp hN
  have hne : Nonempty (V₀ TF.Y Z) :=
    ⟨⟨genPt Z, (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)⟩⟩
  haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG' : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian (pullG TF Z φ) :=
    IsSemiAbelian.pullback _ _ TF.Y.t.semi
  have hcomp : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
    rw [← Category.assoc, hℓφ]
  have hκ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (φ ≫ (barComp TF.Y Z).ι) ℓ
    ((isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr hcomp rfl)
  obtain ⟨κ, hκ, hκψ⟩ : ∃ κ : (pullG TF Z (j₀ TF.Y Z)).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z (j₀ TF.Y Z)) (pullG TF Z φ) ℓ κ ∧ κ ≫ pullψ TF Z φ = pullψ TF Z (j₀ TF.Y Z) :=
    ⟨_, hκ, pullback.lift_fst _ _ _⟩
  have hκw : κ ≫ (pullG TF Z φ).hom = (pullG TF Z (j₀ TF.Y Z)).hom ≫ ℓ := hκ.1.w
  have hM : ∀ γ, ∃ M : (pullG TF Z φ).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z φ) (pullG TF Z φ) (ρ' γ).asIso.hom M ∧ κ ≫ M = n γ ≫ κ := fun γ =>
    exists_isGrpPullback_extend hP.p22 X' (V₀ TF.Y Z) hS ℓ (ρ γ).asIso.hom (ρ' γ).asIso.hom (hρ γ) (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
      (n γ) (hn.1 γ)
  choose m hm hmκ using hM
  have huniq := eq_of_comp_eq_of_isGrpPullback hS ℓ (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
  have hact' : ∀ a : 𝓞 E, κ ≫ ((pullAct TF Z φ).act a).left = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
    intro a
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ) = _ ≫ (κ ≫ pullψ TF Z φ)
      rw [pullAct_pullψ, ← Category.assoc, hκψ, pullAct_pullψ]
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ (pullG TF Z φ).hom) = _ ≫ (κ ≫ (pullG TF Z φ).hom)
      rw [Over.w, hκw, ← Category.assoc, Over.w]
  refine ⟨m, ⟨hm, fun γ a => ?_, fun γ₁ γ₂ => ?_⟩, ?_⟩
  · refine huniq _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, (hm γ).1.w, ← Category.assoc, Over.w]
    · calc κ ≫ ((pullAct TF Z φ).act a).left ≫ m γ
          = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ ≫ m γ := by rw [← Category.assoc, hact', Category.assoc]
        _ = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ n γ ≫ κ := by rw [hmκ]
        _ = n γ ≫ ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
          rw [← Category.assoc, hn.2.1 γ a, Category.assoc]
        _ = n γ ≫ κ ≫ ((pullAct TF Z φ).act a).left := by rw [hact']
        _ = κ ≫ m γ ≫ ((pullAct TF Z φ).act a).left := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · refine huniq _ _ ?_ ?_
    · rw [(hm _).1.w, Category.assoc, (hm γ₁).1.w, ← Category.assoc, (hm γ₂).1.w, Category.assoc, map_mul,
        Aut.mul_asIso]
      rfl
    · calc κ ≫ m (γ₁ * γ₂) = n (γ₁ * γ₂) ≫ κ := hmκ _
        _ = n γ₂ ≫ n γ₁ ≫ κ := by rw [hn.2.2, Category.assoc]
        _ = n γ₂ ≫ κ ≫ m γ₁ := by rw [hmκ]
        _ = κ ≫ m γ₂ ≫ m γ₁ := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · intro γ a b hab w w' hw hw' hwb hwa
    have lift : ∀ v : V₀ TF.Y Z ⟶ (pullG TF Z φ).left, v ≫ (pullG TF Z φ).hom = ℓ →
        ∃ u : V₀ TF.Y Z ⟶ (pullG TF Z (j₀ TF.Y Z)).left, u ≫ (pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _ ∧
          u ≫ pullψ TF Z (j₀ TF.Y Z) = v ≫ pullψ TF Z φ ∧ u ≫ κ = v := by
      intro v hv
      have e : (v ≫ pullψ TF Z φ) ≫ TF.Y.t.G.hom = 𝟙 _ ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (v ≫ (pullG TF Z φ).hom) ≫ _ = _
        rw [hv, Category.id_comp, hcomp]
      refine ⟨pullback.lift _ _ e, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc]
        change _ ≫ (κ ≫ pullψ TF Z φ) = v ≫ pullψ TF Z φ
        rw [hκψ]; exact pullback.lift_fst _ _ _
      · rw [Category.assoc]
        change _ ≫ (κ ≫ (pullG TF Z φ).hom) = v ≫ (pullG TF Z φ).hom
        rw [hκw, ← Category.assoc]
        change (pullback.lift _ _ e ≫ pullback.snd _ _) ≫ ℓ = _
        rw [pullback.lift_snd, Category.id_comp, hv]
    obtain ⟨u, hu1, hu2, hu3⟩ := lift w hw
    obtain ⟨u', hu1', hu2', hu3'⟩ := lift w' hw'
    have := hη γ a b hab u u' hu1 hu1' (by rw [hu2, hwb]) (by rw [hu2', hwa])
    rw [← hu3, ← hu3', Category.assoc, hmκ, ← Category.assoc, this, Category.assoc]
end GlobalTheory.EqvAct
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.equivariant_action_eq_of_agree_on_generators : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  first | exact @_root_.GlobalTheory.EqvAct.equivariant_action_ext | exact _root_.GlobalTheory.EqvAct.equivariant_action_ext | (intros; apply _root_.GlobalTheory.EqvAct.equivariant_action_ext <;> assumption)
end
end
end
