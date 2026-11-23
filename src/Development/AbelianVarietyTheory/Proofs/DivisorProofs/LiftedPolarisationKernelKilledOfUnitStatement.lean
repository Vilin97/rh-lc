module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairsStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
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
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomTrivIff

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoincarePull

theorem exists_hom_triv_iff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (D : Over (Sp R)) [GrpObj D] (Q : LB (A ⊗ D).left), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsDual D A (GlobalTheory.AbDual.swap Q) →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ P : LB (A ⊗ A).left, P.IsLB →
    HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∃ x : A ⟶ D, IsMonHom x ∧ ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (HasGen (P.pull (lift (fst A T) (snd A T ≫ y)).left) ↔ y ≫ x = 1) := by
  intro R _ A _ hA D _ Q q q' L hL aL P hP h₁ h₂
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL aL hL aL
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP a₁ a₂
  refine ⟨x, hx, fun T y ↦ ?_⟩
  have k := GlobalTheory.AbDual.triv_ev_iff hP (fst A T) (snd A T ≫ y)
  rw [GlobalTheory.BirigidLift.evc_of_cls q.isLB hP e, Category.assoc, ← GlobalTheory.AbDual.triv_ev_iff q.isLB] at k
  refine k.trans ⟨fun h ↦ q.eq_one (y ≫ x) h, fun h ↦ ?_⟩
  rw [h, GlobalTheory.AbDual.triv_ev_iff q.isLB, MonObj.comp_one]
  exact GlobalTheory.AbDual.evc_one_right q.isLB q.zero _

end GlobalTheory.PoincarePull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivial

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulUnramified

lemma eq_one_of_pow_eq_one_thick_affine (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (G : Over (Sp C)) [GrpObj G] (n : ℕ)
    (hn : IsUnit (n : C)) (R : CommRingCat.{0}) (g : Spec R ⟶ Sp C) (z : Over.mk g ⟶ G)
    (hz : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g), j ≫ z = 1)
    (hzn : z ^ n = 1) : z = 1 := by
  let φ : CommRingCat.of C ⟶ R := Spec.preimage g
  let K : Ideal C := RingHom.ker π
  let J : Ideal R := Ideal.map φ.hom K
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* R ⧸ J :=
    (Ideal.quotientMap J φ.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ∀ c, ψ (π c) = q (φ c) := by
    intro c
    have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk K c := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
    rfl
  have hJ : RingHom.ker q = J := Ideal.mk_ker
  have hJsq : J ^ 2 = ⊥ := by
    simp only [J, ← Ideal.map_pow]
    change Ideal.map φ.hom (RingHom.ker π ^ 2) = ⊥
    rw [hsq, Ideal.zero_eq_bot, Ideal.map_bot]
  let T₀ : Over (Sp C₀) := Over.mk (spMap ψ)
  have hw : Spec.map (CommRingCat.ofHom q) ≫ g = T₀.hom ≫ spMap π := by
    rw [← Spec.map_preimage g]
    simp only [T₀, spMap, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext c
    exact (hψ c).symm
  let j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g := Over.homMk (Spec.map (CommRingCat.ofHom q)) hw
  have hsurj : Function.Surjective j.left := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap q)
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker q ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hJ, hJsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have hker : RingHom.ker (CommRingCat.ofHom q).hom ^ 2 = ⊥ := by
    change RingHom.ker q ^ 2 = ⊥
    rw [hJ, hJsq]
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  exact eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq (CommRingCat.ofHom q) hker) n hn' z
    (hz T₀ j) hzn

end GlobalTheory.MulUnramified

namespace GlobalTheory.MulUnramified

theorem eq_one_of_pow_eq_one_thick : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  intro C C₀ _ _ π hπ hsq G _ n hn T z hz hzn
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i ↦ ?_
  let k : T.left.affineOpenCover.I₀ := i
  let f : Over.mk (T.left.affineOpenCover.f k ≫ T.hom) ⟶ T := Over.homMk (T.left.affineOpenCover.f k) rfl
  have hfz : (f ≫ z) ^ n = 1 := by
    rw [← MonObj.comp_pow, hzn, comp_one]
  have h := eq_one_of_pow_eq_one_thick_affine C C₀ π hπ hsq G n hn _ _ (f ≫ z)
    (fun T₀ j ↦ by rw [← Category.assoc]; exact hz T₀ _) hfz
  have h' := congrArg (·.left) (h.trans (comp_one f).symm)
  simp only [Over.comp_left] at h'
  exact h'

end GlobalTheory.MulUnramified
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  first | (exact @GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (exact GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (intros; apply GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAmpleKer

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrinThicken

open GlobalTheory.AbDual GlobalTheory.CechPic

theorem evc_comm {S : Scheme.{0}} {X Y : Over S} {M : LB (X ⊗ X).left} (hM : M.IsLB)
    (hc : cls M hM = CechPic.pull (lift (snd X X) (fst X X)).left (cls M hM)) (a b : Y ⟶ X) :
    evc hM a b = evc hM b a := by
  rw [evc, evc]
  conv_lhs => rw [hc]
  rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]

end GlobalTheory.PrinThicken
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerLiftUnit


open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.PrinThicken in
theorem ker_pow_eq_one_of_lift : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → ∀ (l : (G2 A₀).left ⟶ (G2 A).left), Geo.Tor.IsSquare i l → ∀ (P₀ : LB (G2 A₀).left) (P : LB (G2 A).left), P₀.IsLB → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → LBIso (P.pull l) P₀ → ∀ (e : ℕ), IsUnit (e : C) → (∀ (T : Over (Sp C₀)) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ A _ _ i hi hA l hl P₀ P hP₀ hP r₁ r₂ hsymm amp hred e he ker₀
  have csymm : cls P hP = GlobalTheory.CechPic.pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsymm
  have wS : (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l = l ≫ (lift (snd A A) (fst A A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hl.1, GlobalTheory.AbDual.lift_left_fst_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_fst, hl.2]
    · rw [Category.assoc, hl.2, GlobalTheory.AbDual.lift_left_snd_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_snd, hl.1]
  have c₀symm : cls P₀ hP₀ = GlobalTheory.CechPic.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left (cls P₀ hP₀) := by
    have e := (cls_eq_iff (pull_isLB hP l) hP₀).2 hred
    rw [cls_pull hP] at e
    rw [← e, ← pull_comp, wS, pull_comp, ← csymm]
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := GlobalTheory.abelianDualCrystal.1 _ A hA
  obtain ⟨lam, hlam, hiff⟩ := GlobalTheory.PoincarePull.exists_hom_triv_iff C A hA D Q q q' _ (pull_isLB hP _) amp P hP r₁ r₂
  haveI := hlam
  have hiff' : ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ≫ lam = 1 := fun T x hx ↦
    (hiff T x).1 ((triv_ev_iff hP _ _).2 ((evc_comm hP csymm _ _).trans ((triv_ev_iff hP _ _).1 hx)))
  have tors₀ : ∀ (T₀ : Over (Sp C₀)) (z : Over.mk (T₀.hom ≫ spMap π) ⟶ A), z ≫ lam = 1 → z ^ e = 1 := by
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ A₀ := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have k₁ : z₀ ^ e = 1 := ker₀ _ z₀ (by
      have e1 := evc_trR hi hi hl.1 hl.2 hP hP₀ hred (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff _ z).2 hz)
      rw [show pushP hi (s := T₀.hom) rfl z₀ = z from Over.OverMorphism.ext hz₀] at e1
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (GlobalTheory.CechPic.pull s) (e1.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP₀ _ _).2 ((evc_comm hP₀ c₀symm _ _).symm.trans e2))
    have hp : ∀ m : ℕ, (z₀ ^ m).left ≫ i = (z ^ m).left := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero]
        exact one_left_comp hi (s := T₀.hom) rfl
      | succ m ih =>
        rw [pow_succ, pow_succ]
        exact mul_left_comp hi (s := T₀.hom) rfl ih hz₀
    apply Over.OverMorphism.ext
    rw [← hp e, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  intro T x hx
  have hx0 : x ≫ lam = 1 := hiff' T x hx
  have hw0 : (x ^ e) ≫ lam = 1 := by rw [pow_comp, hx0, one_pow]
  have hwC : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ (x ^ e) = 1 := fun T₀ j ↦ by
    rw [comp_pow]
    exact tors₀ T₀ (j ≫ x) (by rw [Category.assoc, hx0, MonObj.comp_one])
  let k := equalizer.ι lam (1 : A ⟶ D)
  have hk : k ≫ lam = 1 := by rw [equalizer.condition, MonObj.comp_one]
  let u : 𝟙_ (Over (Sp C)) ⟶ equalizer lam (1 : A ⟶ D) :=
    equalizer.lift 1 (by rw [MonObj.one_comp, MonObj.comp_one])
  have hww : (x ^ e) ^ e = 1 := by
    have h1 := GlobalTheory.T.comp_eq_of_sqZero_agree_pairs C C₀ π hπ hsq (equalizer lam (1 : A ⟶ D)) A (k ^ e) 1
      (fun T₀ y ↦ by
        rw [comp_pow, MonObj.comp_one]
        exact tors₀ T₀ (y ≫ k) (by rw [Category.assoc, hk, MonObj.comp_one]))
      T (equalizer.lift (x ^ e) (by rw [hw0, MonObj.comp_one])) (toUnit T ≫ u)
      (fun T₀ j ↦ by
        rw [← cancel_mono k, Category.assoc, Category.assoc, Category.assoc,
          show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _,
          show u ≫ k = 1 from equalizer.lift_ι _ _, hwC, MonObj.comp_one, MonObj.comp_one])
      (by rw [comp_pow, MonObj.comp_one, Category.assoc, show u ≫ k = 1 from equalizer.lift_ι _ _,
        MonObj.comp_one, one_pow])
    rw [comp_pow, show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _, MonObj.comp_one] at h1
    exact h1
  exact GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial C C₀ π hπ hsq A e he T (x ^ e) hwC hww

end GlobalTheory.KerLiftUnit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.lifted_polarisation_kernel_killed_of_unit : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → ∀ (l : (G2 A₀).left ⟶ (G2 A).left), Geo.Tor.IsSquare i l → ∀ (P₀ : LB (G2 A₀).left) (P : LB (G2 A).left), P₀.IsLB → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → LBIso (P.pull l) P₀ → ∀ (e : ℕ), IsUnit (e : C) → (∀ (T : Over (Sp C₀)) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @GlobalTheory.KerLiftUnit.ker_pow_eq_one_of_lift | exact GlobalTheory.KerLiftUnit.ker_pow_eq_one_of_lift | (intros; apply GlobalTheory.KerLiftUnit.ker_pow_eq_one_of_lift <;> assumption)
end
end
