module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassReductionCompatible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LogarithmicDerivatives.CrystallineFirstChernExistsUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassReductionCompatible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullTransport
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForE
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleChernClassEqKummerClass

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Zar2

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem zar2 : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := @GlobalTheory.CompanionTheory.ZarCosieve.main

end CrystallineSemistableComparison.Pb
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernJBaseChange

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT.constant_weight_sum_bound

open CH Pb GlobalTheory.CompanionTheory

section Gen
variable {R : Type} [CommRing R] {C D : Type 1} [Category.{0} C] [Category.{0} D] {F : D ⥤ ModuleCat.{0} R}

def incG (S : SubF F) (G : C ⥤ D) : CH.Mor (G ⋙ S.fn) (G ⋙ F) (RingHom.id R) where
  G := 𝟭 C
  τ T := (S.S (G.obj T)).subtype
  nat _ _ := rfl

theorem sub_d (S : SubF F) (G : C ⥤ D) (n : ℕ) (z : Cn (G ⋙ S.fn) n) (w : Cn (G ⋙ S.fn) (n + 1))
    (h : d _ n ((incG S G).pullC n z) = (incG S G).pullC (n + 1) w) : d _ n z = w := by
  rw [(incG S G).d_pullC] at h
  funext s
  exact Subtype.ext (congrFun h s)

def sub (F : D ⥤ ModuleCat.{0} R) {P Q : ObjectProperty D} (h : Q ≤ P) : CH.Mor (P.ι ⋙ F) (Q.ι ⋙ F) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem res_all (F : D ⥤ ModuleCat.{0} R) (P : ObjectProperty D) (hP : ∀ T, P T) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict F P.ι).pull j) := by
  refine CrystallineChernClass.mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) j
  · funext t
    exact congrFun e (P.lift t fun i => hP _)
  · exact ⟨fun t => g (P.lift t fun i => hP _), rfl⟩

theorem bij_three (F : D ⥤ ModuleCat.{0} R) {P Q S : ObjectProperty D} (h : Q ≤ P) (h1 : S ≤ Q) (h2 : S ≤ P) (j : ℕ)
    (s1 : Function.Bijective ((sub F h1).pull j)) (s2 : Function.Bijective ((sub F h2).pull j)) (hP : ∀ T, P T) :
    Function.Bijective ((CH.Mor.restrict F Q.ι).pull j) := by
  have s3 : Function.Bijective ((sub F h).pull j) := by
    have e : (sub F h1).pull j ∘ (sub F h).pull j = (sub F h2).pull j := funext fun x => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    refine (Function.Bijective.of_comp_iff' s1 _).1 ?_
    rw [e]
    exact s2
  have e : (sub F h).pull j ∘ (CH.Mor.restrict F P.ι).pull j = (CH.Mor.restrict F Q.ι).pull j := funext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  rw [← e]
  exact s3.comp (res_all F _ hP j)

end Gen

section Th
variable {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

theorem span_zero (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) : (IdF.span (sP Q).A (0 : b.R)).S T = ⊥ := by
  change Ideal.span {algebraMap b.R ((sP Q).A.obj T) 0} = ⊥
  rw [map_zero, Ideal.span_singleton_eq_bot]

def toJ (Q : ObjectProperty (Thick L)) :
    CH.Mor (Q.ι ⋙ (B.pdS L c 1).fn) (sq (stdI Q (some 1) 0) (stdI Q none 0)) c where
  G := 𝟭 _
  τ T := { toFun := fun x => sqMk _ _ (show T.obj.B from (show (B.pdS L c 1).S T.obj from x).1)
              (Ideal.mem_sup_left (show (B.pdS L c 1).S T.obj from x).2)
           map_add' := fun _ _ => rfl
           map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toJ_τ (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) : Function.Bijective ((toJ c Q).τ T) := by
  refine ⟨fun x y e => ?_, fun y => ?_⟩
  · have h := Ideal.Quotient.eq.1 (congrArg Subtype.val e)
    change _ ∈ (⊥ : Ideal _) ⊔ (IdF.span (sP Q).A (0 : b.R)).S T at h
    rw [span_zero, sup_bot_eq, Ideal.mem_bot, sub_eq_zero] at h
    exact Subtype.ext h
  · obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
    have hy' := hy
    change _ ∈ (sFil Q 1).S T ⊔ (IdF.span (sP Q).A (0 : b.R)).S T at hy'
    rw [span_zero, sup_bot_eq] at hy'
    exact ⟨⟨y, hy'⟩, rfl⟩

theorem toJ_bij (Q : ObjectProperty (Thick L)) (n : ℕ) : Function.Bijective ((toJ c Q).pull n) := by
  refine CrystallineChernClass.mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) n
  · funext s
    have := congrFun e s
    exact (toJ_τ c Q (s.obj (Fin.last n))).1 this
  · choose f hf using fun s : ComposableArrows Q.FullSubcategory n => (toJ_τ c Q (s.obj (Fin.last n))).2 (g s)
    exact ⟨f, funext hf⟩

theorem sub_bij {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ)
    (hb : Function.Bijective (((incl h).sq (incl_std h (some 1) 0) (incl_std h none 0)).pull j)) :
    Function.Bijective ((sub (B.pdS L c 1).fn h).pull j) := by
  have e : (toJ c Q).pull j ∘ (sub (B.pdS L c 1).fn h).pull j =
      ((incl h).sq (incl_std h (some 1) 0) (incl_std h none 0)).pull j ∘ (toJ c P).pull j := funext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  refine (Function.Bijective.of_comp_iff' (toJ_bij c Q j) _).1 ?_
  rw [e]
  exact hb.comp (toJ_bij c P j)

end Th

theorem res_bij {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (hp : p ≠ 0) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤)
    {Λ : Type} [CommRing Λ] (c : Λ →+* R) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.pdS (nlFun γ p X q κ) c 1).fn (CrystallineChernClass.Lifts D).ι).pull j) := by
  have hU : Used (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) := Or.inr ⟨hp, Or.inl rfl⟩
  have h1 : St ⊤ (𝒱D D) ≤ CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D := CrystallineChernClass.st_le_lifts D
  have h1' : CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {sSup (𝒱D D)} := fun T _ =>
    ⟨trivial, _, rfl, by rw [hD]; exact CrystallineChernClass.inU_top T⟩
  have b1 := (zar2 ⊤ hU (𝒱D D) (CrystallineChernClass.Lifts D) h1 h1' (fun T T' φ h _ => CrystallineChernClass.lifts_map D φ h) j).2.1 (some 1) none 0 0
  have h2 : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, CrystallineChernClass.inU_top T⟩
  have b2 := (zar ⊤ hU (𝒱D D) {⊤} h2 (by rintro W rfl; rw [hD]) j).2.1 (some 1) none 0 0
  have h3 : CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, CrystallineChernClass.inU_top T⟩
  have hall : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⊤} T := fun T => ⟨trivial, ⊤, rfl, CrystallineChernClass.inU_top T⟩
  exact bij_three _ h3 h1 h2 j (sub_bij (b := nlBase R I γ p) c h1 j b1) (sub_bij (b := nlBase R I γ p) c h2 j b2) hall

theorem dlog_mem {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ) {v : A} (hv : v - 1 ∈ J) :
    B.dlog δ N v ∈ pdP δ 1 :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨[(k + 1, v - 1)], by simpa using hv, by simp, by simp⟩)

section Core
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I} {D : E.LineData X} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (N : ℕ)

section
variable {C : Type 1} [Category.{0} C] {G : C ⥤ Thick ((B.schFn q).cr b ht κ)}

theorem r_mem (Lf : B.CLift G D) (s : ComposableArrows C 2) : (Lf.r s).val - 1 ∈ (G.obj (s.obj (Fin.last 2))).J := by
  have hfg : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map'_comp 0 1 2
  have := CocCls.red_Rf Lf (s.map' 0 1) (s.map' 1 2)
  rw [← hfg] at this
  exact CocCls.sub_one_mem this

def cocJ (Lf : B.CLift G D) : Cn (G ⋙ (B.pdS _ c 1).fn) 2 :=
  fun s => ⟨Lf.coc c N s, mem_pdS.2 (dlog_mem _ N (r_mem Lf s))⟩

variable (hN : ∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0)
include hN

theorem cocJ_closed (Lf : B.CLift G D) : d _ 2 (cocJ c N Lf) = 0 :=
  sub_d _ G 2 _ _ ((CocCls.closed Lf c N hN).trans (map_zero _).symm)

theorem cocJ_cls (Lf Lf' : B.CLift G D) (hz hz') : (cx _).cls (cocJ c N Lf) hz = (cx _).cls (cocJ c N Lf') hz' := by
  obtain ⟨v, hv⟩ := CocCls.exists_v Lf Lf'
  let y : Cn (G ⋙ (B.pdS _ c 1).fn) 1 := fun s => ⟨CocCls.yc Lf Lf' v c N s,
    mem_pdS.2 (dlog_mem _ N (CocCls.sub_one_mem (CocCls.red_Ef hv (s.map' 0 1))))⟩
  exact ((CrystallineSemistableComparison.P.cls_surj _ 2).2.2.1 _ _ hz hz').2 ⟨y, sub_d _ G 1 y _ (CocCls.d_yc hv c N hN)⟩

end


variable (D) in
def IsFirstChernClassDividedPower (x : H (B.pdS ((B.schFn q).cr b ht κ) c 1).fn 2) : Prop :=
  ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (Lf : B.CLift G D),
    ∃ (z : Cn (G ⋙ (B.pdS _ c 1).fn) 2) (hz : d _ 2 z = 0),
      (∀ s, (show (B.pdS _ c 1).S _ from z s).1 = Lf.coc c N s) ∧
      (cx _).cls z hz = (Mor.restrict (B.pdS _ c 1).fn G).pull 2 x

theorem exu_core (D : E.LineData X) (Q : ObjectProperty (Thick ((B.schFn q).cr b ht κ)))
    (hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T)
    (hbij : Function.Bijective ((CH.Mor.restrict (B.pdS ((B.schFn q).cr b ht κ) c 1).fn Q.ι).pull 2))
    (hN : ∀ (T : Thick ((B.schFn q).cr b ht κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0) :
    ∃! x, IsFirstChernClassDividedPower (q := q) (b := b) (ht := ht) (κ := κ) D c N x := by
  obtain ⟨Λ₀⟩ := clift_ex Q.ι D (fun T => (hQ _).1 T.property)
  have hz₀ := cocJ_closed c N (G := Q.ι) (fun T k hk x _ => by
    change ((k.factorial : ℕ) : (T.obj).B) * _ = 0
    rw [hN _ k hk, zero_mul]) Λ₀
  obtain ⟨x, hx⟩ := hbij.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G Λ₁
    have hG : ∀ T, Q (G.obj T) := fun T => (hQ _).2 ⟨Λ₁.p T, Λ₁.hp T⟩
    have hN' : ∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0 :=
      fun T k hk x _ => by rw [hN _ k hk, zero_mul]
    let Λ' : B.CLift G D := CrystallineChernClass.precomp Λ₀ (Q.lift G hG)
    refine ⟨cocJ c N Λ₁, cocJ_closed c N hN' Λ₁, fun _ => rfl, ?_⟩
    rw [cocJ_cls c N hN' Λ₁ Λ' _ (cocJ_closed c N hN' Λ')]
    have e1 : (CH.Mor.restrict (B.pdS ((B.schFn q).cr b ht κ) c 1).fn G).pull 2 x =
        (CH.Mor.restrict (Q.ι ⋙ (B.pdS ((B.schFn q).cr b ht κ) c 1).fn) (Q.lift G hG)).pull 2
          ((CH.Mor.restrict (B.pdS ((B.schFn q).cr b ht κ) c 1).fn Q.ι).pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hbij.1
    obtain ⟨z, h1, h2, h3⟩ := hy _ Q.ι Λ₀
    obtain rfl : z = cocJ c N Λ₀ := funext fun s => Subtype.ext (h2 s)
    rw [hx, ← h3]

end Core

theorem exu {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ) (hN : (N.factorial : R) = 0) :
    ∃! x, IsFirstChernClassDividedPower (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  have hf : ∀ (T : Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0 := fun T k hk => by
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hk
    have h0 : (k.factorial : R) = 0 := by rw [hm, Nat.cast_mul, hN, zero_mul]
    have := congrArg T.i h0
    rwa [map_natCast, map_zero] at this
  have hb := res_bij (γ := γ) (q := q) (κ := κ) hp D hD c 2
  let Q : ObjectProperty (Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) := CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D
  have hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T := fun T => Iff.rfl
  have hb' : Function.Bijective ((CH.Mor.restrict (B.pdS ((B.schFn q).cr (nlBase R I γ p) rfl κ) c 1).fn Q.ι).pull 2) := hb
  exact exu_core (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) c N D Q hQ hb' hf

open B in
theorem isFirstChernJ_base_change {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b b' : Base}
    {ht : b.t = 1} {ht' : b'.t = 1} {κ : O →+* b.R ⧸ b.I} {κ' : O →+* b'.R ⧸ b'.I}
    (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (τ : b.R ⧸ b.I →+* b'.R ⧸ b'.I)
    (hτ : τ.comp κ = κ') (hs)
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (c' : Λ →+* b'.R) (hc : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    (D : E.LineData X) {N N' : ℕ} (hN : N ≤ N') (hf : ∀ k, N ≤ k → (k.factorial : b'.R) = 0)
    (y : CH.H (pdS ((schFn q).cr b ht κ) c 1).fn 2)
    (hy : IsFirstChernClassDividedPower (q := q) (b := b) (ht := ht) (κ := κ) D c N' y) :
    IsFirstChernClassDividedPower (q := q) (b := b') (ht := ht') (κ := κ') D c' N
      ((pdOm (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) hs) (RingHom.id Λ) hc 1).pull 2 y) := by
  intro C _ G Lf
  let mm := pdOm (c := c) (c' := c') (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) hs) (RingHom.id Λ) hc 1
  let G' : C ⥤ Thick ((schFn q).cr b ht κ) := G ⋙ mm.G
  let Lf' : CLift G' D := { p := Lf.p, hp := Lf.hp, w := Lf.w, hw := Lf.hw }
  obtain ⟨z, hz', hv, hcl⟩ := hy C G' Lf'
  let m4 : CH.Mor (G' ⋙ (pdS _ c 1).fn) (G ⋙ (pdS _ c' 1).fn) (RingHom.id _) :=
    { G := 𝟭 C, τ := fun T => mm.τ (G.obj T), nat := fun φ x => mm.nat (G.map φ) x }
  have hz : CH.d _ 2 (m4.pullC 2 z) = 0 := by rw [m4.d_pullC, hz', map_zero]
  refine ⟨m4.pullC 2 z, hz, fun s => (hv s).trans ?_, ?_⟩
  · refine FirstChernClassFactorial.dlog_eq_of_factorial (G.obj (s.obj (Fin.last 2))).δ hN (fun j hj => ?_) _
    have := congrArg (G.obj (s.obj (Fin.last 2))).i (hf j hj)
    rw [map_natCast, map_zero] at this
    exact this
  · have h1 : (CH.Mor.restrict (pdS _ c' 1).fn G).pull 2 (mm.pull 2 y) =
        m4.pull 2 ((CH.Mor.restrict (pdS _ c 1).fn G').pull 2 y) := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl
    refine Eq.trans ?_ h1.symm
    rw [← hcl]
    rfl

end CrystallineSemistableComparison.HT.constant_weight_sum_bound
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernRestrictionCocycle

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg

theorem res_id_inj {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (j : ℕ) (a b : H F j)
    (h : (Mor.restrict F (𝟭 C)).pull j a = (Mor.restrict F (𝟭 C)).pull j b) : a = b := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact h

theorem two_cls {R : Type} [CommRing R] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R)) (S₀ : SubF F) (S : SubF F') (h₀) (c : R) (h)
    (G : C'' ⥤ C') (x : H S₀.fn 2) (w : Cn ((G ⋙ m.G) ⋙ F) 2)
    (hx : ∃ (z₀ : Cn ((G ⋙ m.G) ⋙ S₀.fn) 2) (hz₀ : d _ 2 z₀ = 0), (∀ s, (show S₀.S _ from z₀ s).1 = w s) ∧
      (cx _).cls z₀ hz₀ = (Mor.restrict S₀.fn (G ⋙ m.G)).pull 2 x)
    (z : Cn (G ⋙ F') 2) (hz : d _ 2 z = 0) (y : H F' 2) (hy : (cx _).cls z hz = (Mor.restrict F' G).pull 2 y)
    (hv : ∀ z' : Cn (G ⋙ F') 2, (∀ s, z' s = m.τ _ (w s)) → ∀ s, z' s = (c • z) s) :
    (Mor.restrict S.fn G).pull 2 ((subMor m S₀ S h₀).pull 2 x) = (Mor.restrict S.fn G).pull 2 ((mulTo c S h).pull 2 y) := by
  obtain ⟨z₀, hz₀, hP, hx⟩ := hx
  obtain ⟨ha, e₂⟩ := GlobalTheory.CompanionTheory.FirstChernComparison.pull_transport S₀.fn S.fn (subMor m S₀ S h₀) G x z₀ hz₀ hx
  obtain ⟨hb, f₂⟩ := GlobalTheory.CompanionTheory.FirstChernComparison.pull_transport F' S.fn (mulTo c S h) G y z hz hy
  refine e₂.symm.trans (Eq.trans ?_ f₂)
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext
    ((congrArg (m.τ _) (hP s)).trans (hv (fun s => m.τ _ (w s)) (fun _ => rfl) s))))

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X} (n : ℕ)

theorem log_eq (Λ : E.Lift G D) (w : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) (hw : Λ.IsCoc n w) (s : ComposableArrows C 2)
    (y : (G.obj (s.obj (Fin.last 2))).1.obj.Acr n)
    (hy : y = B.dlog (B.DD false (G.obj (s.obj (Fin.last 2))).1.obj n) (l * n) ((GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).r s).val) :
    y = E.acrVal G n (s.obj (Fin.last 2)) (w s) :=
  (E.Main.logEx l _ n).2.1 _ _ _ (GlobalTheory.CompanionTheory.FirstChernComparison.st2 false n Λ s y hy) (hw s)

theorem tCo_eq (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) : E.tCo G n 2 z = (tA l ^ 1 : Acris l) • z :=
  congrArg (fun a : Acris l => a • z) (pow_one (tA l : Acris l)).symm

theorem coc_eq (Λ : E.Lift G D) (w : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) (hw : Λ.IsCoc n w)
    (z' : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2)
    (hz' : ∀ s, z' s = (B.βMor (B.schFn q) κ false n).τ _ ((GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).coc ((base l).cris n) (l * n) s))
    (s : ComposableArrows C 2) : z' s = w s :=
  log_eq n Λ w hw s _ (hz' s)

theorem isFirstChernJ_lift_cocycle (x : H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2)
    (hx : constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) x)
    (Λ : E.Lift G D) :
    ∃ (z₀ : Cn (GlobalTheory.CompanionTheory.FirstChernComparison.gG false n G ⋙ (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn) 2) (hz₀ : d _ 2 z₀ = 0),
      (∀ s, (show (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).S _ from z₀ s).1 =
        (GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).coc ((base l).cris n) (l * n) s) ∧
      (cx _).cls z₀ hz₀ = (Mor.restrict (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn
        (GlobalTheory.CompanionTheory.FirstChernComparison.gG false n G)).pull 2 x :=
  hx C (GlobalTheory.CompanionTheory.FirstChernComparison.gG false n G) (GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ)

theorem firstChern_restriction_cocycle (ht : TFil l) (x : H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2)
    (hx : constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) x)
    (Λ : E.Lift G D) (y : MH (PX q κ) n 2) (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) (hz : d _ 2 z = 0)
    (hΛ : Λ.IsCoc n ((tA l ^ 1 : Acris l) • z)) (hy : (cx _).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) G).pull 2 y) :
    (Mor.restrict (TT ((B.schFn q).pt κ) 1 n).fn G).pull 2 ((βMorF (B.schFn q) κ 1 n).pull 2 x) =
      (Mor.restrict (TT ((B.schFn q).pt κ) 1 n).fn G).pull 2 ((tMor ht ((B.schFn q).pt κ) 1 n).pull 2 y) :=
  two_cls (B.βMor (B.schFn q) κ false n) (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1) (TT ((B.schFn q).pt κ) 1 n) _
    (tA l ^ 1) _ G x ((GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).coc ((base l).cris n) (l * n)) (isFirstChernJ_lift_cocycle n x hx Λ) z hz y hy
    (coc_eq n Λ _ hΛ)

end

theorem firstChern_class_general (ht : TFil l) {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l)
    (D : E.LineData X) (n : ℕ) (x : H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2)
    (hx : constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) x)
    (Λ : E.Lift (q := q) (κ := κ) (𝟭 _) D) (y : MH (PX q κ) n 2) (z : Cn (𝟭 _ ⋙ modF (AcrEl (PX q κ) n)) 2) (hz : d _ 2 z = 0)
    (hΛ : Λ.IsCoc n (E.tCo (𝟭 _) n 2 z)) (hy : (cx _).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) (𝟭 _)).pull 2 y) :
    (βMorF (B.schFn q) κ 1 n).pull 2 x = (tMor ht ((B.schFn q).pt κ) 1 n).pull 2 y :=
  res_id_inj _ 2 _ _ (firstChern_restriction_cocycle n ht x hx Λ y z hz ((congrArg (Λ.IsCoc n) (tCo_eq n z)).mp hΛ) hy)

theorem firstChern_compatible_family {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l)
    (D : E.LineData X) (hD : sSup (Pb.𝒱D D) = ⊤) :
    ∃ x : ∀ n, H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2,
      (∀ n, constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) (x n)) ∧
      ∀ n, (pdOm (CrystallineSemistableComparison.SH.redM (B.schFn q) κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) 1).pull 2 (x (n + 1)) = x n := by
  have ex : ∀ n, ∃! x, constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D
      ((base l).cris n) (l * n) x := fun n =>
    constant_weight_sum_bound.exu (B.DD false (base l) n) l (Fact.out : l.Prime).ne_zero q (B.κb κ false n) D hD
      ((base l).cris n) (l * n) (GlobalTheory.CompanionTheory.FirstChernClassFactorial.factorial_acr n _ le_rfl)
  choose x hx hu using ex
  exact ⟨x, hx, fun n => hu n _ (constant_weight_sum_bound.isFirstChernJ_base_change (b := B.bs l false (n + 1)) (b' := B.bs l false n) ((base l).red n.le_succ) rfl
    (B.dd_red false _ n.le_succ) (Ideal.quotientMap _ _ (B.red_le false n.le_succ)) (B.red_κb κ false n.le_succ) (fun _ _ _ => rfl)
    _ _ (B.red_cris _ n.le_succ) D (Nat.mul_le_mul_left l n.le_succ) (fun j hj => GlobalTheory.CompanionTheory.FirstChernClassFactorial.factorial_acr n j hj)
    (x (n + 1)) (hx (n + 1)))⟩

theorem firstChern_family_exists (M : Model l K) (D : E.LineData M.X) (hD : sSup (Pb.𝒱D D) = ⊤) : ∃ x : Fam M 1 2, IsFirstChernClassInFamily D x ∧ Comp x :=
  firstChern_compatible_family M.p (okToOC l K) D hD

theorem h1_lift_of_firstChern (ht : TFil l) {e : E.EtFam l K} (he : EtP e) : ∀ (M : Model l K) (D : E.LineData M.X), Etale D.f →
    sSup (Pb.𝒱D D) = ⊤ → ∀ (r : E.Roots l) (v : M.T 2), IsEtaleFirstChernUntwisted r D v → ∃ x, IsFirstChernClassInFamily D x ∧ IsLift ht e 1 v x :=
  fun M D hf hD r v hv => (firstChern_family_exists M D hD).elim fun x hx =>
    ((E.Main.liftEx l (R.forE l) _ M.X M.p (okToOC l K) _ (𝟭 _) D).2 hf).elim fun Λ =>
      ⟨x, hx.1, hx.2, fun n => (he.c1 M D r v hv _ (𝟭 _) Λ n).elim fun z h => h.elim fun hz h' =>
        firstChern_class_general ht M.p (okToOC l K) D n (x n) (hx.1 n) Λ (e M n 2 (v.lev n)) z hz h'.1 h'.2⟩

end CrystallineSemistableComparison.HT
end
end
end
