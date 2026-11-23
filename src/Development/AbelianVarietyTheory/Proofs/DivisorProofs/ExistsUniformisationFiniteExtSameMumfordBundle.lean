module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetriStatement
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHomStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_baseChange_semiAbelian_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  intro R _ _ _ _ G _ _ hG P A gen hmon hext R' _ _ _ ρ _ hfin
  have hinj : Function.Injective ρ := hfin.2.1

  have gpG₁ : IsGrpPullback ((Over.pullback (spMap ρ)).obj G) G (spMap ρ) (pullback.fst G.hom (spMap ρ)) :=
    isGrpPullback_pullback G (spMap ρ)
  obtain ⟨β₂, hsq, hlam⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ) G ((Over.pullback (spMap ρ)).obj G) _ gpG₁

  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap (hw := pullback.condition) P
    (GlobalTheory.UU.toBase_mul_pullback G (spMap ρ)) _ (pull_isLB P.L.isLB _) _ (GlobalTheory.UU.pullIso_isGen P.L.isLB _)
  let P₁ : GlobalTheory.UU.CP ((Over.pullback (spMap ρ)).obj G) :=
    ⟨⟨P.L.L.pull (pullback.fst G.hom (spMap ρ)), rig, pull_isLB P.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩

  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (GlobalTheory.ArcPull.fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  haveI := hmon
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have gpGen : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ :=
    (GlobalTheory.ArcPull.fracMap_sq hinj).symm.trans (Category.id_comp _)
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G
      (spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp gpG₁).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpGen)
  refine ⟨(Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance, pullback.fst G.hom (spMap ρ), β₂, P₁, A', eA,
    IsSemiAbelian.pullback _ G hG, gpG₁, hsq, mE, ?_, ?_⟩
  · refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb P.L.L (pullback.fst G.hom (spMap ρ))
        (fun _ => pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R'))
        (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  · have hL := P.L.isLB
    have h := hlam P.L.L (P.L.L.pull (pullback.fst G.hom (spMap ρ))) _ (abelian₂ G P.L.L) (𝟙 _) hL (pull_isLB hL _)
      (LB.isLB_linComb hL _ _) (lbIso_refl (pull_isLB hL _)) (LBIso.symm (lbIso_pull_id (LB.isLB_linComb hL _ _)))
    rwa [Category.comp_id] at h

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_baseChange_semiAbelian_cubical_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  first | exact @GlobalTheory.Mum.exists_baseChange_semiAbelian_data | exact GlobalTheory.Mum.exists_baseChange_semiAbelian_data | (intros; apply GlobalTheory.Mum.exists_baseChange_semiAbelian_data <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorus

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_even_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  intro R _ _ _ hR G _ _ hG P A gen hgen hL
  obtain ⟨R', _, _, _, ρ, hR', hρ, hall⟩ := GlobalTheory.T.exists_finiteExtension_splitClosedFibre_rationalTwoTorsion R hR G hG A gen hgen
  obtain ⟨G₁, _, _, β, β₂, P₁, A₁, gen₁, hG₁, hpb, hsq, hgen₁, hL₁, hLam₁⟩ :=
    GlobalTheory.T.exists_baseChange_semiAbelian_cubical_polarised_data R hR G hG P A gen hgen hL R' ρ hR' hρ
  obtain ⟨hsp, htw⟩ := hall G₁ β hpb
  obtain ⟨P₂, A₂, gen₂, hgen₂, hL₂, hLam₂, hev⟩ := GlobalTheory.T.exists_even_translate_two_torsion_split_closed_fibre R' hR' G₁ hG₁ hsp htw P₁ A₁ gen₁ hgen₁ hL₁
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, G₁, inferInstance, inferInstance, β, β₂, P₂, A₂, gen₂,
    hR', hρ, hpb, hsq, hgen₂, hL₂, ?_, hev⟩
  exact LBIso.trans (LB.isLB_linComb P₂.L.isLB _ _) (LB.isLB_linComb P₁.L.isLB _ _)
    (pull_isLB (LB.isLB_linComb P.L.isLB _ _) _) hLam₂ hLam₁

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorusStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_even_translate_order_two_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  first | exact @GlobalTheory.Mum.exists_even_translate | exact GlobalTheory.Mum.exists_even_translate | (intros; apply GlobalTheory.Mum.exists_even_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundle

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UExt

theorem lam_isLB {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) :
    (abelian₂ G L).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem lbIso_pull {X Y : Scheme.{0}} {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q f f rfl)

end GlobalTheory.Mum.UExt


open GlobalTheory.Mum.UExt in
theorem GlobalTheory.Mum.exists_unif_finExt_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨hdvr, hcomp, hchar⟩ := hR
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  obtain ⟨L', hL', hLL'⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G (A.L.pull gen.hom.left) hL
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  have hsym : Out.Sym ((Over.pullback (jK R)).obj G) (L'.pull (pullback.fst G.hom (jK R))) :=
    GlobalTheory.T.symmetric_of_lineBundleIso_pull_groupHom _ _ _ gen.hom hgen A.L _ A.isLB (LB.isLB_pull hL' _) A.sym hLL'
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric R G hG hpr L' hL' hsym
  subst hP
  obtain ⟨R', _, _, _, ρ, G₁, _, _, β, β₂, P₁, A₁, gen₁, hR', hρ, hβ, hsq, hgen₁, hL₁, hLam, hEven⟩ :=
    GlobalTheory.T.exists_even_translate_order_two_torus R ⟨hdvr, hcomp, hchar⟩ G hG P A gen hgen hLL'
  have hB' : Base R' := ⟨hρ.1, @charZero_of_injective_ringHom _ _ _ _ ρ hρ.2.1 hchar⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (Geo.Tor.IsSemiAbelian.pullback (spMap ρ) G hG)
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R' hB' G₁ P₁ hG₁ hEven A₁ gen₁ hgen₁ hL₁
  have hE : LBIso (abelian₂ G P.L.L) PP := GlobalTheory.T.lineBundleIso_mumford_of_generic_extension R G hG P.L.L _ PP P.L.isLB hL hLL' hPP
  refine ⟨R', _, _, _, ρ, D, G₁, _, _, β, β₂, A₁, U, hR', hρ, hβ, hsq, ?_⟩
  rw [hU]
  exact LBIso.trans (lam_isLB G₁ P₁.L.isLB) (LB.isLB_pull (lam_isLB G P.L.isLB) _) (LB.isLB_pull hPP.1 _) hLam
    (lbIso_pull hE β₂)
end
end
