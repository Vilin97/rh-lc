module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoEvEqAtLcmLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateIsoGenericAbelianOfUniformisation

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_tateIso_toA : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
  (I : (letI := H.starRing; TateIsoQ D P.D.toPre P.oD F)),
  ∃ J : TateIso D F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ (letI := H.starRing; P.oA.act a))
      (fun n g g' z => Out.WeilIs P.A.A P.A.L n g g' (unitOn z)),
    (∀ n, J.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ a, P.ToA F n (I.ev n a) (J.ev n a) := by
  intro E _ _ _ H D R _ _ _ hR t P F _ _ _ I
  letI := H.starRing
  have hA : AdmBase R (maximalIdeal R) := hR.1
  have h0 : CharZero R := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hA t P
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT F
  obtain ⟨ev, ev0, evp⟩ : ∃ ev : ℕ → D.La → (TFK (R := R) F ⟶ P.A.A), (∀ a, ev 0 a = 1) ∧
      ∀ n (hn : 0 < n) a, ev n a = f n hn (I.ev n a) :=
    ⟨fun n a => if hn : 0 < n then f n hn (I.ev n a) else 1, fun a => dif_neg (lt_irrefl 0),
      fun n hn a => dif_pos hn⟩
  have add : ∀ n a b, ev n (a + b) = ev n a * ev n b := fun n a b => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ev0, ev0, ev0, _root_.one_mul]
    · rw [evp n hn, evp n hn, evp n hn, f₄ n hn _ _ _ (I.add n hn a b)]
  have zero : ∀ n, ev n 0 = 1 := fun n => by
    have := add n 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := ev, add := add
            lin := fun n c a => ?_, ker := fun n hn a => ?_, onto := fun n hn x => ⟨fun hx => ?_, ?_⟩
            tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    fun _ => rfl, fun j hj x => (f₁ j hj _ _).2 (evp j hj x)⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ev0, ev0]
      have := P.oA.hom c
      exact (MonObj.one_comp _).symm
    · rw [evp n hn, evp n hn, f₅ n hn _ _ _ (I.lin n hn c a)]
  · rw [← zero n, evp n hn, evp n hn, f₃, I.ker n hn]
    simp only [zero_add]
  · obtain ⟨p, hp⟩ := f₂ n hn x hx
    obtain ⟨a, ha⟩ := I.onto n hn p
    exact ⟨a, by rw [evp n hn, (f₃ n hn _ _).2 ha, hp]⟩
  · rintro ⟨a, rfl⟩
    rw [evp n hn, tors]
  · obtain ⟨q, q₁, q₂, q₃⟩ := I.tower n m hn hm a
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level GlobalTheory.firstFiveLaws R _ hA P.D P.A t.G t.semi P.U F n m _ hn hm rfl q
      (I.ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    rw [evp _ hN, evp n hn, (f₁ n hn _ _).1 h, (f₃ n hn _ _).2 q₃]
  · have h := (f₆ n hn _ _ _).1 (I.isom n hn a b)
    rw [← evp, ← evp] at h
    exact h

end GlobalTheory.LowDat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateIsoGenericAbelianOfUniformisationStatement

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
  (I : (letI := H.starRing; TateIsoQ D P.D.toPre P.oD F)),
  ∃ J : TateIso D F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ (letI := H.starRing; P.oA.act a))
      (fun n g g' z => Out.WeilIs P.A.A P.A.L n g g' (unitOn z)),
    (∀ n, J.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ a, P.ToA F n (I.ev n a) (J.ev n a) := by
  first | exact @GlobalTheory.LowDat.exists_tateIso_toA | exact GlobalTheory.LowDat.exists_tateIso_toA | (intros; apply GlobalTheory.LowDat.exists_tateIso_toA <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphismStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

theorem _root_.GlobalTheory.T.linearUniformisation_torsionIsomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso := by
  first | exact @GlobalTheory.FlatTors.torsionIso_holds | exact GlobalTheory.FlatTors.torsionIso_holds | (intros; apply GlobalTheory.FlatTors.torsionIso_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsCompatOfTateIsometries

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem mono_jK_of_domain (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem spMap_comp_jFK {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') :
    spMap σ.toRingHom ≫ jFK (R := R) F = jFK (R := R) F' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem left_eq_of_section (C : UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G)
    (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A)
    (g : Sp F ⟶ tK.G.left) (h1 : g ≫ m1.φ = x.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R))
    (h2 : g ≫ m2.φ = jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ ≫ s.left)
    (g' : Sp F' ⟶ tK.G.left) (h1' : g' ≫ m1.φ = x'.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R))
    (h2' : g' ≫ m2.φ = jFK (R := R) F' ≫ C.y ≫ pullback.fst _ _ ≫ s.left) :
    x'.left = spMap σ.toRingHom ≫ x.left := by
  have := mono_jK_of_domain R
  have w0 : C.P.U.gen.inv.left ≫ pullback.snd C.t.G.hom (jK R) = C.P.A.A.hom := Over.w C.P.U.gen.inv
  have w : x.left ≫ C.P.A.A.hom = jFK (R := R) F := Over.w x
  have w' : x'.left ≫ C.P.A.A.hom = jFK (R := R) F' := Over.w x'
  have c1 : m1.φ ≫ C.t.G.hom = tK.G.hom ≫ jK R := m1.cart.1.w
  have key : ∀ {T : Scheme.{0}} (p : T ⟶ tK.G.left) (z : T ⟶ C.P.A.A.left),
      p ≫ m1.φ = z ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R) → p ≫ tK.G.hom = z ≫ C.P.A.A.hom := by
    intro T p z h
    rw [← cancel_mono (jK R), Category.assoc, ← c1, ← Category.assoc, h, ← w0]
    simp only [Category.assoc, pullback.condition]
  have e1 : g ≫ tK.G.hom = jFK (R := R) F := (key g _ h1).trans w
  have e1' : g' ≫ tK.G.hom = jFK (R := R) F' := (key g' _ h1').trans w'
  have e : g' = spMap σ.toRingHom ≫ g := by
    refine m2.cart.1.hom_ext ?_ ?_
    · have q := congrArg (· ≫ C.y ≫ pullback.fst _ _ ≫ s.left) (spMap_comp_jFK σ)
      exact h2'.trans (q.symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap σ.toRingHom ≫ ·) h2.symm).trans (Category.assoc _ _ _).symm)))
    · rw [Category.assoc, e1, e1', spMap_comp_jFK]
  have e2 : x'.left ≫ C.P.U.gen.inv.left = spMap σ.toRingHom ≫ x.left ≫ C.P.U.gen.inv.left := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← h1, ← h1', e, Category.assoc]
    · simp only [Category.assoc]
      rw [w0, w, w', spMap_comp_jFK]
  have hi : C.P.U.gen.inv.left ≫ C.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e3 := congrArg (· ≫ C.P.U.gen.hom.left) e2
  simpa only [Category.assoc, hi, Category.comp_id] using e3

theorem exists_tateIso_ext (D : Datum H) {S : Scheme.{0}} (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω)
    (x : Sp K ⟶ S) (x' : Sp Ω ⟶ S) (h : spMap i ≫ x = x')
    (I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, (I'.ev n v).left = spMap i ≫ (I.ev n v).left := by
  subst h
  obtain ⟨I', hI⟩ := (TateIsoFieldExt.tateIso_fieldExt abelianSchemeLaws_all.1 E H D S P act K Ω i x).1 I
  exact ⟨I', fun n hn => ⟨(hI n hn).1, fun v => by rw [(hI n hn).2 v]; rfl⟩⟩

end GlobalTheory.LowDat

theorem GlobalTheory.LowDat.level_points_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
  (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F']
  (σ : F →ₐ[FractionRing R] F')
  (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F')),
  GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.XFLevel C tK m1 m2 F' I' →
  ∀ (a : Dw.La) (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A),
    C.P.ToA F l.M' (I.ev l.M' a) x → C.P.ToA F' l.M' (I'.ev l.M' a) x' → x'.left = spMap σ.toRingHom ≫ x.left := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F F' _ _ _ _ _ _ σ I I' hI hI' a x x' hx hx'
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  obtain ⟨J, hJζ, hJ⟩ := GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation Dw R hR C.t C.P F I
  obtain ⟨J', hJζ', hJ'⟩ := GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation Dw R hR C.t C.P F' I'
  obtain ⟨J₂, h₂⟩ := GlobalTheory.LowDat.exists_tateIso_ext Dw C.P.A _ σ.toRingHom _ _ (GlobalTheory.LowDat.spMap_comp_jFK σ) J
  have hM : 0 < l.M := by have := l.three_le; omega
  have hM' : 0 < l.M' := Nat.lcm_pos hM l.A_pos
  have hT := GlobalTheory.T.linearUniformisation_torsionIsomorphism E H R _ hR.1 C.t C.P
  have u : J₂.ev l.M' a = J'.ev l.M' a := by
    refine GlobalTheory.T.tateIso_ev_eq_at_lcm_level Dw l F' _ _ _
      (fun n _ p q d d' => GlobalTheory.weilIs_unique_fieldPoint _ _ _ C.P.A.isLB F' _ n p q d d') J₂ J' ?_ ?_ ?_ a
    · apply Units.ext
      rw [(h₂ _ hM').1, hJζ, hJζ', hI.1, hI'.1]
      simp [GlobalTheory.LowDat.toF]
    · intro b
      obtain ⟨g, g1, g2⟩ := hI.2 _ b _ (Or.inl ⟨rfl, rfl⟩) _ (hJ _ l.A_pos b)
      obtain ⟨g', g1', g2'⟩ := hI'.2 _ b _ (Or.inl ⟨rfl, rfl⟩) _ (hJ' _ l.A_pos b)
      exact Over.OverMorphism.ext (((h₂ _ l.A_pos).2 b).trans
        (GlobalTheory.LowDat.left_eq_of_section C tK m1 m2 σ _ _ _ g g1 g2 g' g1' g2').symm)
    · intro b hb
      obtain ⟨g, g1, g2⟩ := hI.2 _ b _ (Or.inr ⟨rfl, hb, rfl⟩) _ (hJ _ hM b)
      obtain ⟨g', g1', g2'⟩ := hI'.2 _ b _ (Or.inr ⟨rfl, hb, rfl⟩) _ (hJ' _ hM b)
      exact Over.OverMorphism.ext (((h₂ _ hM).2 b).trans
        (GlobalTheory.LowDat.left_eq_of_section C tK m1 m2 σ _ _ _ g g1 g2 g' g1' g2').symm)
  obtain ⟨f, hf, -⟩ := hT F l.M' hM'
  obtain ⟨f', hf', -⟩ := hT F' l.M' hM'
  have e : x = J.ev l.M' a := ((hf _ _).1 hx).trans ((hf _ _).1 (hJ _ hM' a)).symm
  have e' : x' = J'.ev l.M' a := ((hf' _ _).1 hx').trans ((hf' _ _).1 (hJ' _ hM' a)).symm
  rw [e, e', ← u]
  exact (h₂ _ hM').2 a
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsCompatOfTateIsometriesStatement

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.levelPoints_compat_of_tateIsometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
  (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F']
  (σ : F →ₐ[FractionRing R] F')
  (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F')),
  GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.XFLevel C tK m1 m2 F' I' →
  ∀ (a : Dw.La) (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A),
    C.P.ToA F l.M' (I.ev l.M' a) x → C.P.ToA F' l.M' (I'.ev l.M' a) x' → x'.left = spMap σ.toRingHom ≫ x.left := by
  first | exact @GlobalTheory.LowDat.level_points_compat | exact GlobalTheory.LowDat.level_points_compat | (intros; apply GlobalTheory.LowDat.level_points_compat <;> assumption)
end
end
end
