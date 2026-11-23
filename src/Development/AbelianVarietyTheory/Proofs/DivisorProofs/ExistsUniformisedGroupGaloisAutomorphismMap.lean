module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseChangeUniformization
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationCompIdPullbackStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissibleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_pullDeg_identity_self_admissible : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  first | exact @GlobalTheory.DegPullId.exists_isPullDeg_id_self | exact GlobalTheory.DegPullId.exists_isPullDeg_id_self | (intros; apply GlobalTheory.DegPullId.exists_isPullDeg_id_self <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfPullbackDegenerationDataRingAutOver

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SelfPull

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_cast {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] {f₀ f₁ : R₀ →+* R₁}
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} (e : f₀ = f₁) (h : IsPullDeg f₀ D₀ D₁) :
    ∃ h' : IsPullDeg f₁ D₀ D₁, proj h' = proj h ∧ h'.xe = h.xe := by
  subst e; exact ⟨h, rfl, rfl⟩

theorem proj_def {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] {f : R₀ →+* R₁}
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} (h : IsPullDeg f D₀ D₁) :
    proj h = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f) := rfl

theorem exists_self_of_comp {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    {α : R₀ →+* R₁} {β : R₁ →+* R₁} (hα : Function.Injective α) (hβ : Function.Injective β)
    {D₀ : DegPre R₀} {D : DegPre R₁} (h₁ : IsPullDeg α D₀ D) (h : IsPullDeg (β.comp α) D₀ D)
    (hp : proj h = proj h₁) (hx : h.xe = h₁.xe) :
    ∃ h' : IsPullDeg β D D, proj h' ≫ proj h₁ = proj h₁ ∧ ∀ x, h'.xe x = x := by
  have p₁ : IsGrpPullback D.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := GlobalTheory.PullDegUniq.nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegUniq.exists_generic_section h₁
  obtain ⟨hD, hD₁, hD₂, -⟩ := GalMul.exists_isPullDeg_of_val hβ D D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK R₁ ≫ spMap β = genMap hβ ≫ jK R₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK R₁).left ≫ jK R₁ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap hβ ≫ D.xK (xe x) := by
      show (jK R₁ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  refine ⟨hD, by rw [hD₁, e₁, hp], fun x => ?_⟩
  rw [hD₂]
  show h₁.xe.symm (h.xe x) = x
  rw [hx]; exact h₁.xe.symm_apply_apply x

theorem exists_isPullDeg_self_pullOver : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg ρ D D') (σ : Gal ρ),
      ∃ h : IsPullDeg (Gal.hom σ) D' D', PullOver hD h := by
  intro R R' _ _ _ _ ρ hρ D D' hD σ
  have eq : ρ = (Gal.hom σ).comp ρ := RingHom.ext fun r => (σ.2 r).symm
  obtain ⟨h₀, cp, cx⟩ := exists_cast eq hD
  obtain ⟨h, h₁, h₂⟩ := exists_self_of_comp hρ σ.1.injective hD h₀ cp cx
  refine ⟨h, h₂, fun b c hb hc => ?_⟩
  rw [hb, hc, ← proj_def, ← proj_def]
  exact h₁

end GlobalTheory.Mum.SelfPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfPullbackDegenerationDataRingAutOverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_selfPullback_degenerationData_ringAutOver : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg ρ D D') (σ : Gal ρ),
      ∃ h : IsPullDeg (Gal.hom σ) D' D', PullOver hD h := by
  first | exact @GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | exact GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | (intros; apply GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationPullbackToPullDeg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifPull

open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem g_eq_of_isPullDeg {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') : D'.P.g = D.P.g :=
  H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.P.smoothDim)
    (eSec D'.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R'))

theorem exists_pull_of_deg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'),
    AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' →
    ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
      (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      IsSemiAbelian G → ∀ (U : Unif I D A G),
      ∃ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (U' : Unif I' D' A' ((Over.pullback (specOf φ)).obj G)),
        IsPullUnif φ hD (Iso.refl _) U U' := by
  intro R R' _ _ _ _ I I' hR hR' g hg hI D D' hD A G _ _ hG U
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨U', -, -, hPU⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg
    GlobalTheory.abelianSchemeLaws_all.1.polBaseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R' I I' hR hR' g hI D A G hG U D' hD (g_eq_of_isPullDeg hD) ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨A', U', hPU⟩

end GlobalTheory.Mum.UnifPull

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationPullbackToPullDegStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_uniformisation_pullback_to_pullDeg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'),
    AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' →
    ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
      (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      IsSemiAbelian G → ∀ (U : Unif I D A G),
      ∃ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (U' : Unif I' D' A' ((Over.pullback (specOf φ)).obj G)),
        IsPullUnif φ hD (Iso.refl _) U U' := by
  first | exact @GlobalTheory.Mum.UnifPull.exists_pull_of_deg | exact GlobalTheory.Mum.UnifPull.exists_pull_of_deg | (intros; apply GlobalTheory.Mum.UnifPull.exists_pull_of_deg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisation_determined_by_degenerationData_normal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, GlobalTheory.UT.Cl.Determined U := by
  first | exact @GlobalTheory.unif_determined_by_data_normal | exact GlobalTheory.unif_determined_by_data_normal | (intros; apply GlobalTheory.unif_determined_by_data_normal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gal_map_maximalIdeal_le {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] {ρ : R →+* R'} (σ : Gal ρ) :
    (maximalIdeal R').map (Gal.hom σ) ≤ maximalIdeal R' := by
  refine Ideal.map_le_of_le_comap fun x hx => ?_
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply (mem_nonunits_iff.1 ((mem_maximalIdeal x).1 hx))
  have := hu.map (σ.1.symm : R' ≃+* R')
  simpa [Gal.hom] using this

theorem exists_galMap : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ), ∃ a, GalMap hD U' σ a := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG' U' σ
  obtain ⟨hR', hinj, -⟩ := hρ
  have hσi : Function.Injective (Gal.hom σ) := σ.1.injective
  obtain ⟨h, hPO⟩ := GlobalTheory.T.exists_selfPullback_degenerationData_ringAutOver R R' ρ hinj D.toPre D'.toPre hD σ
  obtain ⟨A'', U'', hU''⟩ := GlobalTheory.T.exists_uniformisation_pullback_to_pullDeg R' R' _ _ hR' hR' (Gal.hom σ) hσi (gal_map_maximalIdeal_le σ) D' D' h A' G'
    hG' U'
  obtain ⟨hid, hxe, hem⟩ := GlobalTheory.T.exists_pullDeg_identity_self_admissible R' _ hR' D'
  have hsa : IsSemiAbelian ((Over.pullback (specOf (Gal.hom σ))).obj G') := IsSemiAbelian.pullback _ G' hG'
  obtain ⟨-, bc1, -, -, mbc1, -, hU1, -⟩ :=
    GlobalTheory.T.uniformisation_determined_by_degenerationData_normal R' hR' D' A'' ((Over.pullback (specOf (Gal.hom σ))).obj G') hsa U'' D' A' G' hG' U' hid
  obtain ⟨h', bc, hU, hxe', hem', -, hmon⟩ := GlobalTheory.T.isPullbackUniformisation_comp_id_pullback R' R' _ _ (Gal.hom σ) D' D' D' h hid A' A'' A' G'
    ((Over.pullback (specOf (Gal.hom σ))).obj G') G' (Iso.refl _) bc1 U' U'' U' hU'' hU1
  haveI : IsMonHom bc.hom := hmon (by show IsMonHom (𝟙 _); infer_instance) mbc1
  refine ⟨bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)), ?_, h', bc, rfl, hU, ?_⟩
  · exact ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G' (spMap (Gal.hom σ)))).congr (Category.id_comp _) rfl
  · refine ⟨fun x => by rw [hxe', hxe]; exact hPO.1 x, fun b c hb hc => ?_⟩
    rw [hc, hem', reassoc_of% hem]
    exact hPO.2 b _ hb rfl

end GlobalTheory.Mum
end
end
