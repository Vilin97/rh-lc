module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationEStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBunStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPrincipalPolarisationExtendsSemiAbelianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisationStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionIdempotentFactorTraitUnif

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorMove

theorem isLocalHom_of_finExt {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (h : FinExt ρ) : IsLocalHom ρ := by
  letI := ρ.toAlgebra
  have hi : Algebra.IsIntegral R R' := ⟨fun x => h.2.2.to_isIntegral x⟩
  have hm : (maximalIdeal R').comap ρ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) h.2.2.to_isIntegral (maximalIdeal R'))
  exact ((IsLocalRing.local_hom_tfae ρ).out 1 5).2 hm

theorem exists_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁] [GrpObj G₂]
    {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {β₁ : G₁.left ⟶ G.left} {β₂ : G₂.left ⟶ G.left}
    {β₁₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {β₂₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (h₁ : IsGrpPullback G₁ G f β₁) (h₂ : IsGrpPullback G₂ G (g ≫ f) β₂)
    (s₁ : Geo.Tor.IsSquare β₁ β₁₂) (s₂ : Geo.Tor.IsSquare β₂ β₂₂) :
    ∃ (β : G₂.left ⟶ G₁.left) (β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left),
      IsGrpPullback G₂ G₁ g β ∧ Geo.Tor.IsSquare β β' ∧ β₂₂ = β' ≫ β₁₂ := by
  have w₀ : β₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f := by rw [h₂.1.w, Category.assoc]
  have e : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ β₁ = β₂ := h₁.1.lift_fst _ _ _
  have w : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ G₁.hom = G₂.hom ≫ g := h₁.1.lift_snd _ _ _
  generalize h₁.1.lift β₂ (G₂.hom ≫ g) w₀ = β at e w
  have s : Geo.Tor.IsSquare β (lift (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))).left :=
    ⟨congrArg (fun q => q.left) (lift_fst (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))),
      congrArg (fun q => q.left) (lift_snd (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂)))⟩
  obtain ⟨β', s⟩ : ∃ β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left, Geo.Tor.IsSquare β β' := ⟨_, s⟩
  refine ⟨β, β', IsGrpPullback.cancel h₁ (h₂.congr rfl e.symm) w, s, ?_⟩
  have a : β₂₂ ≫ (fst G G).left = (β' ≫ β₁₂) ≫ (fst G G).left := by
    rw [s₂.1, Category.assoc, s₁.1, ← Category.assoc, s.1, Category.assoc, e]
  have b : β₂₂ ≫ (snd G G).left = (β' ≫ β₁₂) ≫ (snd G G).left := by
    rw [s₂.2, Category.assoc, s₁.2, ← Category.assoc, s.2, Category.assoc, e]
  exact pullback.hom_ext a b

theorem extLam_congr {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {L : LB ((Over.pullback (jK R)).obj G).left} (hL : L.IsLB) {P Q : LB (G2 G).left} (h : ExtLam G L P) (hQ : Q.IsLB)
    (e : LBIso P Q) : ExtLam G L Q :=
  ⟨hQ, fun κ hκ => LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_pull h.1 _) (LB.isLB_pull hQ _) (h.2 κ hκ)
    (GlobalTheory.GenSpread.lbIso_pullback e κ)⟩

theorem exists_finExt_factor_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ D₂' : DegData R₂ (maximalIdeal R₂)) (F₂ : Factor D₂.toPre D₂'.toPre) (A₂' : PolAV (Sp (FractionRing R₂))) (G₂' : Over (Sp R₂)) (_ : GrpObj G₂') (_ : IsCommMonObj G₂') (U₂' : Unif (maximalIdeal R₂) D₂' A₂' G₂') (oA₂ : A₂'.OAct F₂.O) (oG₂ : RingAct G₂' F₂.O) (G₂ : Over (Sp R₂)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (inc₂ : G₂ ⟶ G₂') (pr₂ : G₂' ⟶ G₂) (β₂ : G₂.left ⟶ G.left) (β₂₂ : (G2 G₂).left ⟶ (G2 G).left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), FinExt ρ₂ ∧ Base R₂ ∧ IsSemiAbelian G₂' ∧ U₂'.toUnifPre.OLinear F₂.O F₂.o oA₂ oG₂ ∧ IsSemiAbelian G₂ ∧ IsMonHom inc₂ ∧ IsMonHom pr₂ ∧ inc₂ ≫ pr₂ = 𝟙 G₂ ∧ pr₂ ≫ inc₂ = oG₂.act F₂.e ∧ IsGrpPullback G₂ G (spMap ρ₂) β₂ ∧ Geo.Tor.IsSquare β₂ β₂₂ ∧ IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) ∧ LBIso ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁
    hρ₁ hβ₁ hsq₁ hgen₁ hext
  haveI := hR.2
  have hR₁ : Base R₁ := ⟨hρ₁.1, charZero_of_injective_ringHom hρ₁.2.1⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβ₁ (isGrpPullback_pullback G (spMap ρ₁))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (Geo.Tor.IsSemiAbelian.pullback (f := spMap ρ₁) (G := G) hG)
  obtain ⟨R₂, _, _, _, ρ, hρ, H⟩ := GlobalTheory.T.exists_finiteExtension_trait_uniformisingMumfordBundle R₁ hR₁ G₁ hG₁ A₁ gen₁ hgen₁ _ hext
  have hρ₂ : FinExt (ρ.comp ρ₁) := ⟨hρ.1, hρ.2.1.comp hρ₁.2.1, hρ.2.2.comp hρ₁.2.2⟩
  have hR₂ : Base R₂ := ⟨hρ.1, charZero_of_injective_ringHom hρ₂.2.1⟩
  obtain ⟨D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, β₂, β₂₂, inc₂, pr₂, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    GlobalTheory.FactorPull.factor_baseChange R hR.1 D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr hip hpi R₂ (ρ.comp ρ₁) hρ.1
      hρ₂.2.1 (isLocalHom_of_finExt hρ₂)
  have es : spMap (ρ.comp ρ₁) = spMap ρ ≫ spMap ρ₁ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨β, β', hβ, hsq, hc⟩ := exists_factor hβ₁ (h8.congr es rfl) hsq₁ h9
  obtain ⟨A₂, gen₂, W, _, _, _, φ, GW, _, _, βW, DW, AW, UW, κ, k1, k2, k3, k4, k5, k6, k7, k8⟩ := H G₂ β β' hβ hsq
  have hP := LB.isLB_pull (L := abelian₂ G' U'.LG.L) (LB.isLB_linComb U'.LG.isLB _ _)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have hP₂ := LB.isLB_pull (L := abelian₂ G₂' U₂'.LG.L) (LB.isLB_linComb U₂'.LG.isLB _ _)
    (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ.comp ρ₁, D₂, D₂', F₂, A₂', G₂', inferInstance, inferInstance,
    U₂', oA₂, oG₂, G₂, inferInstance, inferInstance, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, inferInstance, inferInstance,
    inferInstance, φ, GW, inferInstance, inferInstance, βW, DW, AW, UW, κ, hρ₂, hR₂, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    k1, ?_, h10, k3, k4, k5, k6, k7, k8⟩
  exact extLam_congr (LB.isLB_pull A₂.isLB _) k2 hP₂
    (LBIso.trans hP₂ (LB.isLB_pull hP _) k2.1 h10 (GlobalTheory.GenSpread.lbIso_pull_pull hP β' hc)).symm

end GlobalTheory.Mum.FactorMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionIdempotentFactorTraitUnifStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finiteExtension_idempotentFactor_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ D₂' : DegData R₂ (maximalIdeal R₂)) (F₂ : Factor D₂.toPre D₂'.toPre) (A₂' : PolAV (Sp (FractionRing R₂))) (G₂' : Over (Sp R₂)) (_ : GrpObj G₂') (_ : IsCommMonObj G₂') (U₂' : Unif (maximalIdeal R₂) D₂' A₂' G₂') (oA₂ : A₂'.OAct F₂.O) (oG₂ : RingAct G₂' F₂.O) (G₂ : Over (Sp R₂)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (inc₂ : G₂ ⟶ G₂') (pr₂ : G₂' ⟶ G₂) (β₂ : G₂.left ⟶ G.left) (β₂₂ : (G2 G₂).left ⟶ (G2 G).left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), FinExt ρ₂ ∧ Base R₂ ∧ IsSemiAbelian G₂' ∧ U₂'.toUnifPre.OLinear F₂.O F₂.o oA₂ oG₂ ∧ IsSemiAbelian G₂ ∧ IsMonHom inc₂ ∧ IsMonHom pr₂ ∧ inc₂ ≫ pr₂ = 𝟙 G₂ ∧ pr₂ ≫ inc₂ = oG₂.act F₂.e ∧ IsGrpPullback G₂ G (spMap ρ₂) β₂ ∧ Geo.Tor.IsSquare β₂ β₂₂ ∧ IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) ∧ LBIso ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait | exact GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait | (intros; apply GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactor

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_lbExt_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ExtLam G (A.L.pull gen.hom.left) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (L₁ : LB G₁.left), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr h1 h2 A gen hgen hext W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW κ hpb hκ hiso
  obtain ⟨L₁, hL₁, hiso₁⟩ := GlobalTheory.T.symmetricPrincipalPolarisation_extends_semiAbelian R hR.1 G hG A gen hgen _ hext
  have hsp : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  refine ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, G, inferInstance, inferInstance, 𝟙 _, 𝟙 _, L₁,
    ⟨hR.1, Function.injective_id, RingHom.Finite.id R⟩, ?_, by simp, hL₁, ?_⟩
  · haveI : IsMonHom (Iso.refl G).hom := (inferInstance : IsMonHom (𝟙 G))
    exact (isGrpPullback_of_iso (Iso.refl G)).congr hsp.symm rfl
  · exact LBIso.trans (LB.isLB_pull hL₁ _) hL (LB.isLB_pull hL _) hiso₁ (GlobalTheory.TInj.GenPull.pull_id_iso hL)

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExtension_symmBundle_extension_on_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ExtLam G (A.L.pull gen.hom.left) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (L₁ : LB G₁.left), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) := by
  first | exact @GlobalTheory.Mum.exists_finExt_lbExt_of_factor | exact GlobalTheory.Mum.exists_finExt_lbExt_of_factor | (intros; apply GlobalTheory.Mum.exists_finExt_lbExt_of_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfIdempotentFactorBiex

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finExt_evenCP_of_factor_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₂, _, _, _, ρ₂, D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, _, _, _,
    φ, GW, _, _, βW, DW, AW, UW, κ, hρ₂, hR₂, hG₂', hOL₂, hG₂, hinc₂, hpr₂, hip₂, hpi₂, hβ₂, hsq₂, hgen₂, hE₂, hPP₂,
    hW, hφ, hφl, hβW, hκ, hUW⟩ :=
    GlobalTheory.T.exists_finiteExtension_idempotentFactor_trait_unif R hR D D' F A' G' hG' U' oA oG hOL G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₃, _, _, _, ρ₃, G₃, _, _, β₃, κ₃, L₃, hρ₃, hβ₃, hκ₃, hL₃, hL₃iso⟩ :=
    GlobalTheory.T.exists_finiteExtension_symmBundle_extension_on_factor R₂ hR₂ D₂ D₂' F₂ A₂' G₂' hG₂' U₂' oA₂ oG₂ hOL₂ G₂ hG₂ inc₂ pr₂ hinc₂ hpr₂ hip₂ hpi₂ A₂ gen₂ hgen₂ hE₂
      W hW φ hφ hφl GW βW DW AW UW κ hβW hκ hUW
  obtain ⟨R₉, _, _, _, ρ, G₉, _, _, β₉, β₉₂, P, A₉, gen₉, hρ, hβ₉, hsq₉, hG₉, hlam, hev, hgen₉, hiso₉⟩ :=
    GlobalTheory.T.exists_evenCubicalStructure_of_genericPolarisation_extension R₂ hR₂ G₂ hG₂ A₂ gen₂ hgen₂ _ hE₂ W φ GW βW DW AW UW κ hW hφ hφl hβW hκ hUW R₃ ρ₃ G₃ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃
      hL₃ hL₃iso
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hΛ₂ : (abelian₂ G₂' U₂'.LG.L).IsLB := LB.isLB_linComb U₂'.LG.isLB _ _
  refine ⟨R₉, inferInstance, inferInstance, inferInstance, ρ.comp ρ₂, G₉, inferInstance, inferInstance, β₉ ≫ β₂,
    β₉₂ ≫ β₂₂, P, A₉, gen₉, ⟨hρ.1, hρ.2.1.comp hρ₂.2.1, hρ.2.2.comp hρ₂.2.2⟩, ?_, ?_, hG₉, ?_, hev, hgen₉, hiso₉⟩
  · rw [spMap_comp]
    exact hβ₉.comp hβ₂
  · exact ⟨by rw [Category.assoc, hsq₂.1, ← Category.assoc, hsq₉.1, Category.assoc],
      by rw [Category.assoc, hsq₂.2, ← Category.assoc, hsq₉.2, Category.assoc]⟩
  · have a := GlobalTheory.GenSpread.lbIso_pullback hPP₂ β₉₂
    have b := GlobalTheory.GenSpread.lbIso_pull_pull (pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ (a' := β₉₂ ≫ β₂₂) rfl
    have c := GlobalTheory.GenSpread.lbIso_pull_pull hΛ (β₉₂ ≫ β₂₂)
      (a' := (β₉₂ ≫ β₂₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) rfl
    have hL : (abelian₂ G₉ P.L.L).IsLB := LB.isLB_linComb P.L.isLB _ _
    refine LBIso.trans hL (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB hΛ _) hlam ?_
    refine LBIso.trans (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB hΛ _) a ?_
    refine LBIso.trans (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ _)
      (LBIso.symm b) (LBIso.symm c)

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfIdempotentFactorBiexStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_evenCubicalStructure_of_idempotentFactor_biextension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  first | exact @GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam | exact GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam | (intros; apply GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactor

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_cp_factor_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₁, _, _, _, ρ₁, G₁, _, _, β₁, β₁₂, A₁, gen₁, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_evenCubicalStructure_of_idempotentFactor_biextension R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁
    h1 h2 h3 h4 h5

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀)))) := by
  first | exact @GlobalTheory.Mum.exists_finExt_cp_factor_even | exact GlobalTheory.Mum.exists_finExt_cp_factor_even | (intros; apply GlobalTheory.Mum.exists_finExt_cp_factor_even <;> assumption)
end
end
