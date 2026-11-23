module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.RigidPullbackIdentification
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Lemma
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.UniformizationBaseChange

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification

section Carries

variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X) {K : Type} [Fintype K]

def CarriesFam (w : LB.Iso L' (L.pull F)) (p' : K → (Y ⟶ X')) (p : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L' p' ε)) (b : LB.Gen (LB.LinComb L p ε)) : Prop :=
  (∀ k, p' k ≫ F = p k) ∧
  ∀ (j : K → L.ι) (j' : K → L'.ι) (V : Y.Opens) (hb : V ≤ LB.wchart L p j)
    (ha : V ≤ LB.wchart L' p' j')
    (hw : ∀ k, V ≤ p' k ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j k, j' k)),
    res hb (b.s j) =
      (∏ k, res (hw k) (pullU (p' k) _ (w.s (fun _ => j k, j' k))) ^ ε k) * res ha (a.s j')

end Carries

section Pull

open scoped CategoryTheory.Obj

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

structure GrpPull (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] where
  F : G'.left ⟶ G.left
  cart : IsPullback F G'.hom G.hom (specOf φ)
  F_one : eSec G' ≫ F = specOf φ ≫ eSec G
  F_mul : (μ[G']).left ≫ F =
    pullback.map G'.hom G'.hom G.hom G.hom F F (specOf φ) cart.w.symm cart.w.symm ≫ (μ[G]).left

structure RigPull {φ : R →+* R'} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] (pG : GrpPull φ G G')
    (L : RigLB G) (L' : RigLB G') where
  w : LB.Iso L'.L (L.L.pull pG.F)
  w_gen : w.IsGen
  w_rig : CarriesAt L.L L'.L pG.F w (eSec G') (specOf φ ≫ eSec G) pG.F_one 1 L'.rig
    (LB.pullGen L.L _ _ L.rig (specOf φ))

variable {I : Ideal R} {I' : Ideal R'}

omit [IsDomain R] [IsDomain R'] in
lemma pow_le_comap {φ : R →+* R'} (hI : I ≤ I'.comap φ) (n : ℕ) :
    I ^ n ≤ (I' ^ n).comap φ :=
  (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow φ n)

abbrev thickSpec {φ : R →+* R'} (hI : I ≤ I'.comap φ) (e : ℕ) :
    Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I' ^ (e + 1)) φ (pow_le_comap hI (e + 1))))

omit [IsDomain R] [IsDomain R'] in
lemma thickSpec_comp {φ : R →+* R'} (hI : I ≤ I'.comap φ) (e : ℕ) :
    thick R' I' e ≫ specOf φ = thickSpec hI e ≫ thick R I e := by
  simp only [thick, thickSpec, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.quotientMap_comp_mk]

def GrpPull.thickF {φ : R →+* R'} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] (pG : GrpPull φ G G')
    (hI : I ≤ I'.comap φ) (e : ℕ) : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left :=
  pullback.map G'.hom (thick R' I' e) G.hom (thick R I e) pG.F (thickSpec hI e) (specOf φ)
    pG.cart.w.symm (thickSpec_comp hI e)

structure UnifPull {φ : R →+* R'} (hI : I ≤ I'.comap φ) {D : DegData R I} {D' : DegData R' I'}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    (pD : PullIdent φ D.toPre D'.toPre) (pG : GrpPull φ G G')
    (U : Unif I D A G) (U' : Unif I' D' A' G') where
  bundle : RigPull pG U.LG U'.LG
  q_eq : ∀ e : ℕ, (U'.gt e).pG.left ≫ pD.F = pG.thickF hI e ≫ (U.gt e).pG.left
  t_eq : ∀ (e : ℕ) (χ : D'.toPre.X),
    CarriesFam D.toPre.P.L D'.toPre.P.L pD.F pD.w
      (D'.toPre.Oφ (U'.gt e).pG χ)
      (fun k => pG.thickF hI e ≫ D.toPre.Oφ (U.gt e).pG (pD.xe χ) k) Oinvε
      ((U'.gt e).t χ)
      (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t (pD.xe χ)) (pG.thickF hI e))
  w_eq : ∀ (e : ℕ) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι)
    (V : (thickObj R' I' e G').left.Opens)
    (h₁ : V ≤ (U'.gt e).pG.left ⁻¹ᵁ
      (LB.div (D.toPre.P.L.pull pD.F) D'.toPre.P.L).U (fun _ => jM, jM'))
    (h₂ : V ≤ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left)
      (U'.LG.L.pull (fstG I' e G').left)).U (fun _ => jM', fun _ => jL'))
    (h₃ : V ≤ pG.thickF hI e ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
      (U.LG.L.pull (fstG I e G).left)).U (fun _ => jM, fun _ => jL))
    (h₄ : V ≤ (fstG I' e G').left ⁻¹ᵁ
      (LB.div (U.LG.L.pull pG.F) U'.LG.L).U (fun _ => jL, jL')),
    res h₁ (pullU (U'.gt e).pG.left _ (pD.w.s (fun _ => jM, jM'))) *
        res h₂ ((U'.w e).s (fun _ => jM', fun _ => jL')) =
      res h₃ (pullU (pG.thickF hI e) _ ((U.w e).s (fun _ => jM, fun _ => jL))) *
        res h₄ (pullU (fstG I' e G').left _ (bundle.w.s (fun _ => jL, jL')))

def GenericInPsiLocus (φ : R →+* R') (D : DegPre R) : Prop :=
  ∃ (W : (Spec (CommRingCat.of R)).Opens) (_ : PsiOn D W) (g : (TK R').left ⟶ (TW W).left),
    g ≫ W.ι = jK R' ≫ specOf φ

end Pull


open scoped CategoryTheory.Obj in
def UnifBaseChange : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (I : Ideal R) (I' : Ideal R') (_ : AdmBase R I) (_ : AdmBase R' I')
    (φ : R →+* R') (hI : I ≤ I'.comap φ)
    (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (_ : IsSemiAbelian G)
    (U : Unif I D A G) (_ : GenericInPsiLocus φ D.toPre)
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (pG : GrpPull φ G G')
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (_ : A'.g = A.g)
    (gen' : (Over.pullback (jK R')).obj G' ≅ A'.A) (_ : IsMonHom gen'.hom)
    (L' : RigLB G') (pL : RigPull pG U.LG L')
    (_ : ∃ w : LB.Iso (A'.L.pull gen'.hom.left) (L'.L.pull (pullback.fst G'.hom (jK R'))),
      w.IsGen),
    ∃ (D' : DegData R' I') (pD : PullIdent φ D.toPre D'.toPre) (U' : Unif I' D' A' G')
      (hL : U'.LG = L') (P : UnifPull hI pD pG U U'),
      U'.gen = gen' ∧ (hL ▸ P.bundle : RigPull pG U.LG L') = pL

section Basic₂

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPullSubsingleton

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifPullCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange (CarriesFam GrpPull RigPull UnifPull GenericInPsiLocus UnifBaseChange)
open GlobalTheory.PullDegCompare
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Bundle

end Bundle

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']

omit [IsDomain R] [IsDomain R'] in
theorem isGrpPullback_of_bc (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) :
    IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
  ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl


variable [IsCommMonObj G] [IsCommMonObj G']

variable {I : Ideal R} {I' : Ideal R'}

variable {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}

end Main

end GlobalTheory.UnifPullCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectGroupIdentification

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.pulled_lowObj_grp_ident : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] (ev : V →+* K), ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ev) π₁ → ∃ θ : o'.t.G.left ⟶ B'.left, IsGrpPullback o'.t.G B' (𝟙 _) θ ∧ LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) ∧ (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ ev o' m₁ B' _ π₁ hπ
  obtain ⟨g, hD, -, hxe, -⟩ := hDiv
  have hsp : spMap ev ≫ specOf iw = spMap (ev.comp iw) := by
    simp [spMap, specOf, ← Spec.map_comp]
  have hii : IsGrpPullback Q.P.A L.D.P.A (specOf iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    GlobalTheory.UnifPullCompare.isGrpPullback_of_bc hD.e hD.e_hom
  have h₂ : IsGrpPullback B' L.D.P.A (spMap (ev.comp iw))
      (π₁ ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    (IsGrpPullback.comp hπ hii).congr hsp rfl
  have h₁ : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
    (IsGrpPullback.comp m₁.cart L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨θe, hθm, hθ⟩ := grpPullback_iso h₁ h₂
  refine ⟨θe.hom.left, ?_, ?_, ?_⟩
  · haveI := hθm
    exact isGrpPullback_of_iso θe
  · have A : LBIso o'.t.PP.L (L.o.t.PP.L.pull m₁.toSABMap.φ) := GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m₁.toSABMap
    have B : LBIso (L.o.t.PP.L.pull m₁.toSABMap.φ) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull L.ab.2.2 _ rfl
    have C : LBIso Q.P.L (L.D.P.L.pull (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw))) :=
      ⟨hD.w, hD.w_gen⟩
    have C' : LBIso (Q.P.L.pull (θe.hom.left ≫ π₁)) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull C _ (by rw [← hθ]; simp only [Category.assoc])
    exact LBIso.trans o'.t.PP.isLB (pull_isLB L.D.P.isLB _) (pull_isLB Q.P.isLB _)
      (LBIso.trans o'.t.PP.isLB (pull_isLB L.o.t.PP.isLB _) (pull_isLB L.D.P.isLB _) A B) C'.symm
  · intro x a hx hc
    apply hii.1.hom_ext
    · have hcp : (Q.c a).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
          specOf iw ≫ (L.D.c (l.M' • e a)).left := by
        have := hD.c_pr a
        rw [hxe a] at this
        exact this
      simp only [Category.assoc]
      rw [hθ, hc, hcp, ← Category.assoc, hsp]
    · have hq : (Q.c a).left ≫ Q.P.A.hom = 𝟙 _ := Over.w (Q.c a)
      have hB : θe.hom.left ≫ B'.hom = o'.t.G.hom := Over.w θe.hom
      simp only [Category.assoc]
      rw [hπ.1.w, ← Category.assoc θe.hom.left, hB, ← Category.assoc x, hx, hq]
      simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectGroupIdentificationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulledLowerObject_group_identification : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] (ev : V →+* K), ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ev) π₁ → ∃ θ : o'.t.G.left ⟶ B'.left, IsGrpPullback o'.t.G B' (𝟙 _) θ ∧ LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) ∧ (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) := by
  first | exact @GlobalTheory.UCanon.pulled_lowObj_grp_ident | exact GlobalTheory.UCanon.pulled_lowObj_grp_ident | (intros; apply GlobalTheory.UCanon.pulled_lowObj_grp_ident <;> assumption)
end
end
