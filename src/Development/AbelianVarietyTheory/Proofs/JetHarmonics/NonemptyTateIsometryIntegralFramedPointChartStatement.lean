module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BidegreeTwoJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.TateTransport

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def TateTransportStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (Dw : Datum H),
    letI := H.starRing
    ∀ I₀ : TateIso Dw F (TF (R := R) F ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c)),
      ∃ I₁ : TateIso Dw F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
          (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c)),
        ∀ n, I₁.ζ n = I₀.ζ n

theorem weil_move (hW : WeilSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {φ : P.A.A.left ⟶ t.G.left} (hp : IsGrpPullback P.A.A t.G (jK R) φ)
    (w : LB.Iso P.A.L (t.PP.L.pull φ)) (hw : w.IsGen)
    (n : ℕ) (x y : TFK (R := R) F ⟶ P.A.A) (hx : x ^ n = 1) (hy : y ^ n = 1) (c : Γ(Sp F, ⊤)ˣ)
    (hG : WeilIs t.G t.PP.L n (pushPt hp.1.w x) (pushPt hp.1.w y) c) : WeilIs P.A.A P.A.L n x y c := by
  obtain ⟨c', hc', -⟩ := (hW (Sp (FractionRing R)) P.A n (TFK (R := R) F)).1 x y hx hy
  intro p
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hpx₀, hpy₀⟩, hall₀⟩ := hG p
  obtain ⟨V', hpV', -, hall'⟩ := hc' p
  have hsub : Subsingleton (Spec (CommRingCat.of F)) := inferInstance
  have hVV : V = V' := by
    ext q
    rw [@Subsingleton.elim _ hsub q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  subst hVV
  have hτ : 𝟙 _ ≫ (overRes (T := TF (R := R) F) V).hom = (overRes (T := TFK (R := R) F) V).hom ≫ jK R := by
    rw [Category.id_comp]; exact (Category.assoc _ _ _).symm
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (overResι (T := TFK (R := R) F) V ≫ x).left ≫ φ := by
    rw [hpx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc]; rfl
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (overResι (T := TFK (R := R) F) V ≫ y).left ≫ φ := by
    rw [hpy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc]; rfl
  obtain ⟨θx, hθx, mx⟩ := exists_theta_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V)
    hp (𝟙 _) hτ t.PP.isLB P.A.isLB w hw n (overResι (T := TFK (R := R) F) V ≫ x) θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := exists_theta_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V)
    hp (𝟙 _) hτ t.PP.isLB P.A.isLB w hw n (overResι (T := TFK (R := R) F) V ≫ y) θy₀ mvy
  have hm := commIsOf_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V) hp (𝟙 _) hτ t.PP.isLB P.A.isLB w n θx₀ θy₀ θx θy (by rw [hθx]; exact mvx)
    (by rw [hθy]; exact mvy) mx my (unitRes (T := TF (R := R) F) V c) (unitRes (T := TFK (R := R) F) V c) (fun Z r z => by rw [Category.comp_id]; rfl)
    (hall₀ θx₀ θy₀ hpx₀ hpy₀)
  have hcc := commIsOf_unique P.A.isLB θx θy _ _ hm (hall' θx θy hθx hθy)
  refine ⟨V, hpV, ⟨θx, θy, hθx, hθy⟩, fun θx' θy' h₁ h₂ => ?_⟩
  rw [hcc]
  exact hall' θx' θy' h₁ h₂

theorem tateTransport_holds (hW : WeilSt) : TateTransportStatement := by
  intro E _ _ _ H R _ _ I t P F _ _ Dw
  letI := H.starRing
  intro I₀
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  obtain ⟨w, hw⟩ := hL
  let Φ := pushHom gpG (TFK (R := R) F)
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (gpG.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (gpG.1.lift x₀.left (jFK (R := R) F) (Over.w x₀)) (gpG.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gpG.1.lift_fst _ _ _)⟩
  let Φe : (TFK (R := R) F ⟶ P.A.A) ≃* (TF (R := R) F ⟶ t.G) := MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦ : ∀ x, Φe x = pushPt gpG.1.w x := fun x => rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have hact : ∀ x a, Φe (x ≫ P.oA.act a) = Φe x ≫ t.act.act a := fun x a => by
    apply Over.OverMorphism.ext
    show (x ≫ P.oA.act a).left ≫ _ = (pushPt gpG.1.w x).left ≫ (t.act.act a).left
    rw [Over.comp_left, Category.assoc, actA]; rfl
  have hpow : ∀ n, 0 < n → ∀ a, (Φe.symm (I₀.ev n a)) ^ n = 1 := fun n hn a => by
    rw [← map_pow, (I₀.onto n hn _).2 ⟨a, rfl⟩, map_one]
  refine ⟨
    { ζ := I₀.ζ
      ζ_prim := I₀.ζ_prim
      ζ_pow := I₀.ζ_pow
      ev := fun n a => Φe.symm (I₀.ev n a)
      add := fun n a b => by simp only [I₀.add, map_mul]
      lin := fun n c a => by
        show Φe.symm (I₀.ev n (c • a)) = Φe.symm (I₀.ev n a) ≫ P.oA.act c
        apply Φe.injective
        rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
        exact I₀.lin n c a
      ker := fun n hn a => (map_eq_one_iff _ Φe.symm.injective).trans (I₀.ker n hn a)
      onto := fun n hn x => by
        rw [← map_eq_one_iff Φe Φe.injective, map_pow, I₀.onto n hn]
        exact exists_congr fun a => Φe.symm_apply_eq.symm
      tower := fun n m hn hm a => by rw [← map_pow, I₀.tower n m hn hm a]
      isom := fun n hn a b => by
        have h := I₀.isom n hn a b
        rw [← Φe.apply_symm_apply (I₀.ev n a), ← Φe.apply_symm_apply (I₀.ev n b), hΦ, hΦ] at h
        exact weil_move hW P F gpG w hw n _ _ (hpow n hn a) (hpow n hn b) _ h }, fun n => rfl⟩

end ReciprocityTheory.ChartRestriction.G.H1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.IntegralTate

theorem nonempty_tateIso_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S')
    (I : TateIso D k (Over.mk (x ≫ f) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c))) :
    Nonempty (TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => WeilIs t'.G t'.PP.L n g g' (unitOn c))) := by
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I⟩
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc

theorem nonempty_tateIso_of_intChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], Nonempty (TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P F _ _ _ _ _ _
  letI := io.toAlgebra
  obtain ⟨β, hβ⟩ := GlobalTheory.LevelFibre.exists_spMap ((jFK (R := T.V) F ≫ y.1.x) ≫ Xo.s)
  obtain ⟨-, I₀, -⟩ := Xo.univ.geom F (jFK (R := T.V) F ≫ y.1.x) β hβ
  obtain ⟨I₁⟩ := nonempty_tateIso_pull C.I.m1 (jFK (R := T.V) F) I₀
  obtain ⟨I₂, -⟩ := GlobalTheory.LevelFibre.exists_tate_push_comm C.I.m2 (jFK (R := T.V) F) _ rfl
    (ObjPull.pushEquiv C.I.m2.cart (Over.mk (jFK (R := T.V) F))) (fun _ => rfl) I₁
  obtain ⟨I₃, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.tateTransport_holds GlobalTheory.firstFiveLaws.1.weil E H T.V _ C.I.G P F Dw I₂
  exact ⟨I₃⟩

end GlobalTheory.IntegralTate
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], Nonempty (TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))) := by
  first | exact @GlobalTheory.IntegralTate.nonempty_tateIso_of_intChart | exact GlobalTheory.IntegralTate.nonempty_tateIso_of_intChart | (intros; apply GlobalTheory.IntegralTate.nonempty_tateIso_of_intChart <;> assumption)
end
end
