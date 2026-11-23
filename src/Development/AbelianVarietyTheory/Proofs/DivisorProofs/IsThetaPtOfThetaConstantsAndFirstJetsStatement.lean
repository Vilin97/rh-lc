module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionFirstPower
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGenSecIffFibres

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.GenSecFibre

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem mem_nonzeroLocus_pullS (a : ℤ) (h : T' ⟶ T) (th : LB.Sec (LPow P.A P.L a T)) (z : (T' ⊗ P.A).left) :
    z ∈ nonzeroLocus (pullS P.A a h th) ↔ (h ▷ P.A).left z ∈ nonzeroLocus th := by
  have e : ∀ j, z ∈ (LPow P.A P.L a T').U j → (IsUnit (gs (𝟙 _) z _ ((pullS P.A a h th).f j)) ↔
      IsUnit (gs (𝟙 _) ((h ▷ P.A).left z) _ (th.f j))) := fun j hj => by
    have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a) th (h ▷ P.A).left
      (fun _ => whisker_snd_left P.A h) (𝟙 _) z j hj
    rw [Category.id_comp] at q
    have q' := q.trans (gs_stalkMap (h ▷ P.A).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left P.A h) j hj) _)
    exact (iff_of_eq (congrArg IsUnit q')).trans (isUnit_map_iff _ _)
  rw [mem_nonzeroLocus, mem_nonzeroLocus]
  refine exists_congr fun j => ⟨fun ⟨hj, u⟩ => ⟨?_, (e j hj).1 u⟩, fun ⟨hj, u⟩ => ?_⟩
  · exact wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) j hj
  · have hj' := mem_wchart_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) z j hj
    exact ⟨hj', (e j hj').2 u⟩

theorem exists_mem_nonzeroLocus (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : IsGenSec P.A P.L 1 th) (p : T.left) :
    ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th := by
  let w : Spec (CommRingCat.of (T.left.residueField p)) ⟶ T.left := T.left.fromSpecResidueField p
  let h : Over.mk (w ≫ T.hom) ⟶ T := Over.homMk w rfl
  have : IsAffine (Over.mk (w ≫ T.hom)).left := inferInstanceAs (IsAffine (Spec _))
  have h₀ := ThetaCoset.ne_zero_of_isGenSec hS P (w ≫ T.hom) (isGenSec_pullS P hS h H)
  have := P.isAb.smooth
  have : Smooth (fst (Over.mk (w ≫ T.hom)) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst (w ≫ T.hom) P.A.hom))
  have : IsReduced (Over.mk (w ≫ T.hom) ⊗ P.A).left :=
    isReduced_scheme_of_smooth_of_isIntegrallyClosed (T.left.residueField p) (fst (Over.mk (w ≫ T.hom)) P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 h th) := by
    by_contra hn
    refine h₀ (Subtype.ext (funext fun j => ?_))
    exact eq_zero_of_basicOpen_eq_bot _ (le_bot_iff.1 fun z hz => hn ⟨z, Opens.mem_iSup.2 ⟨j, hz⟩⟩)
  refine ⟨(h ▷ P.A).left z, ?_, (mem_nonzeroLocus_pullS P 1 h th z).1 hz⟩
  rw [← Scheme.Hom.comp_apply, (isPullback_whisker P.A h).w, Scheme.Hom.comp_apply]
  exact (T.left.range_fromSpecResidueField p).le ⟨_, rfl⟩

theorem map_sub_eq_zero' {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M]
    [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (s t : M) (b : M') (a c d₀ e₀ : R) (d e : R')
    (ht : φ t = d • b) (hs : φ s = e • b) (hd : σ d₀ = σ a * d) (he : σ e₀ = σ c * e) :
    φ ((d₀ * c) • s - (e₀ * a) • t) = 0 := by
  rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_mul, map_mul, ht, hs, hd, he, smul_smul, smul_smul,
    sub_eq_zero]
  congr 1
  ring

theorem isGenSec_of_fibres (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : ∀ p : T.left, ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th) :
    IsGenSec P.A P.L 1 th := by
  intro s
  let I : Ideal Γ(T.left, ⊤) := (Submodule.span Γ(T.left, ⊤)
    {SecM.ofSec P.A th}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T.left, ∃ f ∈ I, p ∈ T.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    have rep : ∀ x : SecM P.A P.L 1 (overRes W), ∃ d : Γ((overRes W).left, ⊤), x = d • (c hq.default :) := fun x => by
      have := c.sum_repr x
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    obtain ⟨d, hd⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A th))
    obtain ⟨e, he⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A s))
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * d := exists_pow_mul_extend f d
    obtain ⟨n, e₀, he₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * e := exists_pow_mul_extend f e
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f ((d₀ * f ^ n) • SecM.ofSec P.A s - (e₀ * f ^ m) • SecM.ofSec P.A th)
      (map_sub_eq_zero' _ _ _ _ _ _ _ _ _ d e hd he hd₀ he₀)
    have hu : p ∈ T.left.basicOpen d₀ := by
      obtain ⟨q, hqp, hq0⟩ := H p
      obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback (isPullback_whisker P.A (overResι W)) q
        ⟨p, hp⟩ hqp
      subst hz
      obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 ((mem_nonzeroLocus_pullS P 1 (overResι W) th z).2 hq0)
      have k := (congrArg (fun x => gs (𝟙 _) z _ (x.1 j)) hd).trans (PushInv.gs_smul P.A P.L _ 1 d _ j z hj)
      have u₁ : IsUnit (gs (fst (overRes W) P.A).left z ⊤ d) := isUnit_of_mul_isUnit_left (k ▸ u)
      rw [gs_stalkMap _ z ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial] at u₁
      have u₂ : (fst (overRes W) P.A).left z ∈ (overRes W).left.basicOpen d := (Scheme.mem_basicOpen_top _ _ _).2 u₁
      have u₃ : (⟨p, hp⟩ : (overRes W).left) ∈ (overResι W).left ⁻¹ᵁ T.left.basicOpen d₀ := by
        rw [Scheme.preimage_basicOpen_top, hd₀, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]
        refine ⟨?_, hz' ▸ u₂⟩
        change p ∈ T.left.basicOpen (f ^ m)
        rw [Scheme.mem_basicOpen_top] at hp ⊢
        rw [map_pow]
        exact hp.pow _
      exact u₃
    refine ⟨f ^ N * (d₀ * f ^ n), Submodule.mem_span_singleton.2 ⟨f ^ N * (e₀ * f ^ m), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · rw [Scheme.mem_basicOpen_top] at hp hu ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hu.mul (hp.pow _))
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem isGenSec_iff_fibres : Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (R : Type) [CommRing R] (y : Sp R ⟶ S) (th : LB.Sec (Out.LPow P.A P.L 1 (Over.mk y))), Out.IsGenSec P.A P.L 1 th ↔ ∀ p : Sp R, ∃ q : (Over.mk y ⊗ P.A).left, (fst (Over.mk y) P.A).left q = p ∧ q ∈ Out.nonzeroLocus th := by
  intro h S P R _ y th
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Spec _))
  exact ⟨exists_mem_nonzeroLocus P h.secBaseChangeAny,
    isGenSec_of_fibres P (T := Over.mk y) h.secBaseChangeAny⟩

end GlobalTheory.GenSecFibre
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJets

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ThetaOfJet

open GlobalTheory.MBLow.JetUniq

theorem isGenSec_of_polAVSectionInverseImage {K : Type} [Field K] (x : KeyIn K)
    (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
    (h : IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th) : IsGenSec x.P.A x.P.L 1 th := by
  have e : th = TrSec.thSec x.P x.th := by
    refine NormTheta.sec_ext fun j => ?_
    obtain ⟨i, rfl⟩ : ∃ i : x.P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact (h i (TrSec.chart_le x.P _)).trans (TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th i (TrSec.chart_le x.P _)).symm
  subst e
  haveI : Subsingleton (Over.mk (𝟙 (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine (GenSecFibre.isGenSec_iff_fibres firstFiveLaws.2.1 (Sp K) x.P K (𝟙 _) _).2 fun p => ?_
  obtain ⟨z, -, hz⟩ := x.th_ne p
  exact ⟨_, Subsingleton.elim _ _, TrSec.nonzero_thSec x.P x.th z hz⟩

theorem ptSecT_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (z : baseOver (Sp R) ⟶ A) :
    (ptSecT A z).left = z.left ≫ toProd A := by
  rw [toProd, ← Over.comp_left, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

open GlobalTheory.MBLow.JetUniq

theorem fnOf_valR_id {K : Type} [Field K] (f : Γ(Sp K, ⊤)) : GlobalTheory.Ex.fnOf (valR (𝟙 (Sp K)) ⊤ f) = f := by
  have h : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  rw [valR, dite_eq_left h]
  simp [GlobalTheory.Ex.fnOf, Scheme.Hom.appLE]
  rfl

theorem isThetaPt_of_thJet : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  intro K _ x g hg m hm hK I pt ϑ J hJ
  obtain ⟨th, hth, U, t, i₀, c, hUT, hi₀, H⟩ := hJ
  have hLaw : Laws := firstFiveLaws.1
  have hL := x.P.isLB
  let T : Over (Sp K) := baseOver (Sp K)
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ x.P m
  have e₁ : (snd T x.P.A).left ≫ (mulA x.P.A m).left = (snd T x.P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T x.P.A).left, (snd T x.P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen x.P.L ![𝟙 x.P.A.left, (mulA x.P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T x.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A T m) (snd T x.P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT x.P.A (U i).pt) (translPt x.P.A (U i).pt)
    (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) (U i).φ (U i).isGen s₁
  have ht : ∀ i, t i = s₂ i := fun i => NormTheta.sec_ext (tr_unique x.P x.rig hm (fun _ => rfl) (hUT i).1 (hUT i).1
    (hUT i).2 ⟨α, s₁, hα, hn, hs₁, hs₂ i⟩)
  let τ := rigT x.P.A x.P.L x.rig T ((m ^ 2 : ℕ) : ℤ)
  have hτ : τ.IsGen := NormTheta.rigT_isGen x.rig_gen _
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) 1 τ hτ
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := fun z hz => hi₀ hz
  let r : K := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  let V₁ := (x.P.L.LinComb (fun _ : Fin 1 => (1 : T ⟶ x.P.A).left) fun _ => ((m ^ 2 : ℕ) : ℤ)).U fun _ => i₀
  let q : K := valR (𝟙 (Sp K)) V₁ (τ.s fun _ => i₀).val
  have hq₀ : q ≠ 0 := (isUnit_valR (𝟙 (Sp K)) V₁ (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hp : (ptSecT x.P.A (1 : T ⟶ x.P.A)).left = eSec x.P.A ≫ toProd x.P.A := by
    rw [ptSecT_left, NormTheta.one_left]
    exact congrArg (· ≫ toProd x.P.A) (Category.id_comp _)
  let j₀ : Fin g := ⟨0, hg ▸ x.g_pos⟩
  have hval : ∀ i, valR (𝟙 (Sp K)) ⊤ (w i) * q = r ^ (m ^ 2) * ϑ i := fun i => by
    have e2 := GlobalTheory.ZH.TorsReg.valR_valueAt x.P.A x.P.L _ (hw i) (𝟙 (Sp K)) i₀ (by
      rintro _ ⟨z, rfl⟩; exact k₀ trivial)
    rw [Category.id_comp, hp, ← ht i] at e2
    let V := LB.wchart x.P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) x.P.A).left) fun _ => i₀
    have e : (valR (epsLift (x.v (Fin.cast hg.symm j₀))) V ((t i).f fun _ => i₀)).fst = r ^ (m ^ 2) * ϑ i := by
      have := congrArg TrivSqZeroExt.fst (H i j₀)
      simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr,
        add_zero] at this
      exact this
    rw [epsLift_eq] at e
    erw [GlobalTheory.HolHom.valR_comp (A := DualNumber K) (x.v (Fin.cast hg.symm j₀)).left (toProd x.P.A) V] at e
    rw [fst_valR (x.basis.1 _) (le_toProd k₀)] at e
    erw [← GlobalTheory.HolHom.valR_comp (A := K) (eSec x.P.A) (toProd x.P.A) V] at e
    exact e2.symm.trans e
  have un : ∀ a : K, a ≠ 0 → IsUnit (fnOf a) := fun a ha =>
    (IsUnit.mk0 _ ha).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hmu : IsUnit (m : Γ(T.left, ⊤)) := by
    have := un m hK
    rwa [GlobalTheory.Ex.fnOf, map_natCast] at this
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ThetaSeries.isThetaPt_of_data x.P hm hmu (Nat.cast_pow m 2) th s₁ α τ U s₂ w
    (un _ (div_ne_zero hq₀ (pow_ne_zero (m ^ 2) hr₀))).unit
    ⟨isGenSec_of_polAVSectionInverseImage x th hth, hα, hτ, hs₁, fun i => (hUT i).1, hs₂, hw, fun i => ?_⟩
  rw [IsUnit.unit_spec, ← fnOf_valR_id (w i), ← map_mul]
  congr 1
  field_simp
  linear_combination (hval i).symm

end GlobalTheory.MBLow.ThetaOfJet
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJetsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  first | exact @GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet | exact GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet | (intros; apply GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet <;> assumption)
end
end
