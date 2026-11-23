module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMorImg
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullFrob
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedCmp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcOneH
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcPullHc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCommutesGaloisAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulFil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePull
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwAcrFromBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsPullbackEmptyProductOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubsingletonH

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHClsEq

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisOne

universe w w' v u v' u'

theorem mapH_cls_eq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) (n : ℕ) (a : K.X n) (ha : K.d n a = 0) (b : L.X n) (hb : L.d n b = 0) (e : φ.f n a = b) :
    φ.mapH n (K.cls a ha) = L.cls b hb := by
  subst e
  exact CrystallineSemistableComparison.P.mapH_cls φ n a ha hb

theorem pull_oneH {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {A : C ⥤ CommAlgCat.{w} R} {B : C' ⥤ CommAlgCat.{w'} R}
    (m : CH.Mor (CH.modF A) (CH.modF B) (RingHom.id R))
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : B.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH B :=
  mapH_cls_eq m.hom 0 _ _ _ _ (funext fun _ => h _)

theorem β_one {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) :
    β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n) :=
  pull_oneH (βMor F κ k n) fun _ => rfl

end GlobalTheory.CompanionTheory.CrisOne
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiBaseLe

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisFrob

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redLe (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem phi_base_le {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((phiPt F κ m).app B₀ ((basePt F _ (red_κb κ true h)).app B₀ y)).1.2 =
      ((basePt F _ (red_κb κ true h)).app B₀ ((phiPt F κ n).app B₀ y)).1.2 := by
  rw [SH.phi_snd F κ m B₀ _ (l_zero y.1.1), SH.base_snd, SH.base_snd, SH.phi_snd F κ n B₀ _ (l_zero y.1.1)]

theorem red_phi_le : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) := by
  intro l _ O _ F κ m n h j x
  unfold redHc phiHc redMor phiMorC
  exact cr_square (SH.phiM F κ m) (redLe F κ true h) (redLe F κ true h) (SH.phiM F κ n) ((base l).phi_cris m)
    (red_cris _ h) (red_cris _ h) ((base l).phi_cris n) ((pdOk_frob _).red_acr h) (phi_base_le F κ h) j x

end GlobalTheory.CompanionTheory.CrisFrob
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCup

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupBeta
open CrystallineSemistableComparison.CH
universe w u v u' v'

theorem pull_cup {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w} R) (m : Mor (modF A) (modF A') (RingHom.id R))
    (hm : ∀ T (x y : A.obj (m.G.obj T)), m.τ T ((mulP A).μ _ x y) = (mulP A').μ T (m.τ T x) (m.τ T y))
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    m.pull n ((mulP A).cup h x y) = (mulP A').cup h (m.pull p x) (m.pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat hm h x y

theorem beta_cup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ}
    (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j) :
    β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  pull_cup (OcA F κ k n) (AcrEl (F.pt κ) n) (βMor F κ k n) (fun _ _ _ => rfl) h x y

end GlobalTheory.CompanionTheory.CupBeta
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapFactor

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaCmp

theorem quotientMap_factor {B : Type} [CommRing B] {I J K : Ideal B} (hJ : I ≤ J) (hK : I ≤ K) (h : J ≤ K.comap (RingHom.id B))
    (w : B ⧸ I) : Ideal.quotientMap K (RingHom.id B) h (Ideal.Quotient.factor hJ w) = Ideal.Quotient.factor hK w := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem pt_uJ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (A : PAlg l) (n : ℕ) (y : F.Pt.obj (CommRingCat.of A.U))
    (h : JJ false A n ≤ (JJ true A n).comap (RingHom.id _)) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap (JJ true A n) (RingHom.id _) h)) (F.Pt.map (CommRingCat.ofHom (uJ false A n)) y) =
      F.Pt.map (CommRingCat.ofHom (uJ true A n)) y := by
  have e : (Ideal.quotientMap (JJ true A n) (RingHom.id _) h).comp (uJ false A n) = uJ true A n :=
    RingHom.ext fun x => quotientMap_factor (fil_le false A n) (fil_le true A n) h _
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

theorem β_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x := by
  intro l _ O _ F κ n j x
  have e : β F κ true n j ((cmpMor F κ n).pull j x) =
      ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n)).pull j x :=
    pull_pull (RingHom.id _) (cmpMor F κ n) (βMor F κ true n) j x
  refine e.trans ?_
  refine (cr_pull_eq (βMor F κ false n) ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n))
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (T.1.obj.dp_fil_pfil n) ?_) ?_ ?_ j x).symm
  · intro h
    exact pt_uJ F T.1.obj n T.2.1 h
  · intro T T' f z; rfl
  · intro T z; rfl

end GlobalTheory.CompanionTheory.BetaCmp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcCup

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupTrans

theorem omMor_cup {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} (h : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    {p q s : ℕ} (e : p + q = s) (x : CH.H (OM L c) p) (y : CH.H (OM L c) q) :
    (omMor m (RingHom.id Λ) h).pull s ((CH.mulP (OA L c)).cup e x y) =
      (CH.mulP (OA L' c')).cup e ((omMor m (RingHom.id Λ) h).pull p x) ((omMor m (RingHom.id Λ) h).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (CH.mulP (OA L c)) (CH.mulP (OA L' c')) m.functor (omMor m (RingHom.id Λ) h).τ
    (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).nat
    (omMor m (RingHom.id Λ) h).nat (omMor m (RingHom.id Λ) h).nat (fun _ _ _ => rfl) e x y

theorem redHc_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) {i j s : ℕ} (e : i + j = s) (x : Hc F κ k m i) (y : Hc F κ k m j), redHc F κ k h s ((CH.mulP (OcA F κ k m)).cup e x y) = (CH.mulP (OcA F κ k n)).cup e (redHc F κ k h i x) (redHc F κ k h j y) := by
  intro l _ O _ F κ k m n h i j s e x y
  exact omMor_cup _ _ e x y

end GlobalTheory.CompanionTheory.CupTrans
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsC

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.cp_red : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x) :=
  @GlobalTheory.CompanionTheory.BetaRed.beta_red

theorem CrystallineSemistableComparison.B.P.cp_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) :=
  @GlobalTheory.CompanionTheory.BetaGal.β_gal

theorem CrystallineSemistableComparison.B.P.cp_phi : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ true n j), β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x) :=
  @GlobalTheory.CompanionTheory.CrysPhi.phi_beta

theorem CrystallineSemistableComparison.B.P.cp_pull : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j), β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  @GlobalTheory.CompanionTheory.BetaPull.beta_pull

theorem CrystallineSemistableComparison.B.P.cp_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x :=
  @GlobalTheory.CompanionTheory.BetaCmp.β_cmp

theorem CrystallineSemistableComparison.B.P.cp_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ} (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j), β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) = (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  @GlobalTheory.CompanionTheory.CupBeta.beta_cup

theorem CrystallineSemistableComparison.B.P.cp_one : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ), β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n) :=
  @GlobalTheory.CompanionTheory.CrisOne.β_one

theorem CrystallineSemistableComparison.B.P.cp_red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j :=
  @GlobalTheory.CompanionTheory.CrisFil.red_fil

theorem CrystallineSemistableComparison.B.P.cp_smul_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l), (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j :=
  @GlobalTheory.CompanionTheory.BetaFil.smul_fil

theorem CrystallineSemistableComparison.B.P.ch_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) :=
  @GlobalTheory.CompanionTheory.CrisTransition.redHc_galHc

theorem CrystallineSemistableComparison.B.P.ch_phi : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) :=
  @GlobalTheory.CompanionTheory.CrisFrob.red_phi_le

theorem CrystallineSemistableComparison.B.P.ch_pull : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F' κ k m j), redHc F κ k h j (pullHc κ u k m j x) = pullHc κ u k n j (redHc F' κ k h j x) :=
  @GlobalTheory.CompanionTheory.CrisTransition.redHc_pullHc

theorem CrystallineSemistableComparison.B.P.ch_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) {i j s : ℕ} (e : i + j = s) (x : Hc F κ k m i) (y : Hc F κ k m j), redHc F κ k h s ((CH.mulP (OcA F κ k m)).cup e x y) = (CH.mulP (OcA F κ k n)).cup e (redHc F κ k h i x) (redHc F κ k h j y) :=
  @GlobalTheory.CompanionTheory.CupTrans.redHc_cup

theorem CrystallineSemistableComparison.B.P.ch_one : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m), redHc F κ k h 0 (CH.oneH (OcA F κ k m)) = CH.oneH (OcA F κ k n) :=
  @GlobalTheory.CompanionTheory.CrisUnit.redHc_oneH

theorem CrystallineSemistableComparison.B.P.ch_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j), redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) :=
  @GlobalTheory.CompanionTheory.CrisCmp.main

theorem CrystallineSemistableComparison.B.P.firstChern_compatible : ∀ (l : ℕ) [Fact l.Prime], FirstChernCompatible l :=
  @GlobalTheory.CompanionTheory.FirstChernComparison.main
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FirstChernCompatibleL

section

@[expose] public section

namespace CrystallineSemistableComparison.B

variable (l : ℕ) [Fact l.Prime]

theorem main : Main l := main_of (D.out l)

theorem compat : Compat l :=
  ⟨P.cp_red, P.cp_gal, P.cp_phi, P.cp_pull, P.cp_cmp, P.cp_cup, P.cp_one, P.cp_red_fil, P.cp_smul_fil⟩

theorem compatH : CompatH l := ⟨P.ch_gal, P.ch_phi, P.ch_pull, P.ch_cup, P.ch_one, P.ch_cmp⟩

theorem firstChern_compatible_l : FirstChernCompatible l := P.firstChern_compatible l

end CrystallineSemistableComparison.B
end
end
