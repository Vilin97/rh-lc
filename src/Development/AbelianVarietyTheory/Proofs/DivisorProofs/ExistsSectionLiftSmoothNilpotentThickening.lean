module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.RingTheory.DividedPowers.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift

section

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms

variable {R : Type} [CommRing R] {A W K : Type} [CommRing A] [CommRing W] [CommRing K]
  [Algebra R A] [Algebra R W] [Algebra R K]

theorem exists_lift_nil [Algebra.FormallySmooth R A] [Algebra.FinitePresentation R A]
    (ρ : W →ₐ[R] K) (hsurj : Function.Surjective ρ) (hnil : ∀ a ∈ RingHom.ker ρ, IsNilpotent a)
    (φ : A →ₐ[R] K) : ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  classical
  obtain ⟨n, f, hf, hfg⟩ : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective f ∧
      (RingHom.ker f.toRingHom).FG := by
    first
    | exact Algebra.FinitePresentation.out
    | (obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
       exact ⟨n, f, hf, hfg⟩)
  choose w hw using fun i : Fin n => hsurj (φ (f (MvPolynomial.X i)))
  let Φ : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hΦ : ρ.comp Φ = φ.comp f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Φ, hw]
  obtain ⟨s, hs⟩ := hfg
  let J : Ideal W := Ideal.span (Φ '' (s : Set (MvPolynomial (Fin n) R)))
  have hker : RingHom.ker f.toRingHom ≤ J.comap Φ := by
    rw [← hs, Ideal.span_le]
    intro p hp
    exact Ideal.mem_comap.mpr (Ideal.subset_span ⟨p, hp, rfl⟩)
  have hJker : J ≤ RingHom.ker ρ := by
    rw [Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have hpk : p ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span hp
    rw [RingHom.mem_ker] at hpk
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 := congrArg (fun g => g p) hΦ
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    have h2 : f p = 0 := hpk
    rw [h2, map_zero]
  have hJnil : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨s.image Φ, by rw [Finset.coe_image]⟩]
    intro a ha
    exact mem_nilradical.mpr (hnil a (hJker ha))
  have hcond : ∀ a ∈ RingHom.ker f, ((Ideal.Quotient.mkₐ R J).comp Φ) a = 0 := by
    intro a ha
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hker ha
  let g : A →ₐ[R] W ⧸ J := (Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ)
    hcond).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  refine ⟨Algebra.FormallySmooth.lift J hJnil g, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := hf a
  have hmk := Algebra.FormallySmooth.mk_lift J hJnil g (f p)
  have e2 : g (f p) = Ideal.Quotient.mk J (Φ p) := by
    have e0 : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p) = Ideal.Quotient.mk (RingHom.ker f) p := by
      rw [AlgEquiv.symm_apply_eq]
      first
      | rfl
      | simp
    show (Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ) hcond)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p)) = _
    rw [e0]
    rfl
  have e3 : ρ (Algebra.FormallySmooth.lift J hJnil g (f p)) = ρ (Φ p) := by
    have h4 : Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J hJnil g (f p)) = Ideal.Quotient.mk J (Φ p) :=
      hmk.trans e2
    rw [Ideal.Quotient.eq] at h4
    have h5 := hJker h4
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h5
    exact h5
  rw [AlgHom.comp_apply, e3]
  exact congrArg (fun g' => g' p) hΦ

end ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSectionLiftBasicOpenAffine

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem awayMap_surjective_of_surjective (π : R →+* R₀) (hπ : Function.Surjective π) (f : R) :
    Function.Surjective (Localization.awayMap π f) :=
  Localization.awayMap_surjective_iff.2 fun a =>
    (hπ a).elim fun b hb => ⟨b, 0, by simp [hb]⟩

theorem isNilpotent_of_awayMap_eq_zero (π : R →+* R₀) (hnil : IsNilpotent (RingHom.ker π)) (f : R)
    (x : Localization.Away f) (hx : Localization.awayMap π f x = 0) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have h1 : algebraMap R₀ (Localization.Away (π f)) (π a) = 0 := by
    have := congrArg (Localization.awayMap π f) hs
    rw [map_mul, hx, zero_mul] at this
    rw [← RingHom.comp_apply, ← hc, RingHom.comp_apply, ← this]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (π f)) _ _).1 h1
  have hmem : f ^ k * a ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_mul, map_pow]; exact hk
  have h0 : (f ^ k * a) ^ N = 0 := by
    have := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    exact Ideal.mem_bot.1 this
  have hu : IsUnit (algebraMap R (Localization.Away f) (s * f ^ k)) := by
    rw [map_mul, map_pow]
    exact (IsLocalization.map_units _ s).mul ((IsLocalization.Away.algebraMap_isUnit f).pow k)
  refine ⟨N, (hu.pow N).mul_left_eq_zero.1 ?_⟩
  rw [← mul_pow, map_mul, ← mul_assoc, hs, ← map_mul, mul_comm a, ← map_pow, h0, map_zero]

theorem exists_liftIn_unfolded : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤ := by
  intro R R₀ _ _ π hπ hnil X hX g₀ hg p
  haveI := hX
  have hker : RingHom.ker π ≤ p.asIdeal := fun a ha => by
    obtain ⟨N, hN⟩ := hnil
    have := Ideal.pow_mem_pow ha N
    rw [hN] at this
    exact p.isPrime.mem_of_pow_mem N ((Ideal.mem_bot.1 this) ▸ p.asIdeal.zero_mem)
  obtain ⟨p₀, hp₀⟩ : p ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [_root_.range_comap_of_surjective (R := R) R₀ π hπ]
    exact hker
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g₀ p₀)) isOpen_univ
  obtain ⟨_, ⟨r, rfl⟩, hp₀r, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p₀) (u := {q : PrimeSpectrum R₀ | g₀ q ∈ V}) hxV (g₀ ⁻¹ᵁ V).isOpen
  obtain ⟨f, rfl⟩ := hπ r
  refine ⟨f, ?_, V, hV, ?_⟩
  · rw [← hp₀]
    exact hp₀r
  have hsurj := awayMap_surjective_of_surjective π hπ f
  have hnilL := isNilpotent_of_awayMap_eq_zero π hnil f
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have hx0 : Set.range (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) ⊆ V := by
    rintro _ ⟨q, rfl⟩
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (π f)) (π f)).subset ⟨q, rfl⟩
  obtain ⟨x, h₁, h₂⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen X.hom (isAffineOpen_top (Sp R)) hV
    (fun _ _ => trivial) (CommRingCat.ofHom (Localization.awayMap π f))
    (spMap (algebraMap R (Localization.Away f))) (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀)
    (by
      rw [Category.assoc, hg, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact (congrArg (fun φ : R →+* Localization.Away (π f) => φ a) hc).symm)
    (fun _ _ => trivial) hx0 (by
      intro R' A _ _ _ _ _ _ π' hπ' φ
      exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil π'
        (fun c => (hsurj c).imp fun b hb => (hπ' b).trans hb)
        (fun a ha => hnilL a (by rw [RingHom.mem_ker] at ha; rw [← ha]; exact (hπ' a).symm)) φ)
  refine ⟨x, h₂, h₁, top_unique fun q _ => ?_⟩
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (Localization.awayMap π f)) := by
    rw [_root_.range_comap_of_surjective (R := Localization.Away f) _ _ hsurj]
    intro a ha
    obtain ⟨n, hn⟩ := hnilL a ha
    exact (q : PrimeSpectrum (Localization.Away f)).isPrime.mem_of_pow_mem n (hn ▸ q.asIdeal.zero_mem)
  show x q ∈ V
  have : x q = (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) q' := by
    rw [← h₁]
    exact congrArg x hq'.symm
  rw [this]
  exact hx0 ⟨q', rfl⟩

theorem exists_liftIn : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V :=
  exists_liftIn_unfolded

end GlobalTheory.SecLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSectionLiftBasicOpenAffineStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V := by
  first | exact @GlobalTheory.SecLift.exists_liftIn | exact GlobalTheory.SecLift.exists_liftIn | (intros; apply GlobalTheory.SecLift.exists_liftIn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionLiftNilpotentOfSqZero

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

theorem lift_of_nilpotent_of_sqZero :
    (∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e) →
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  intro H
  suffices key : ∀ n : ℕ, ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
      RingHom.ker π ^ n = ⊥ →
      ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) →
      Smooth X.hom →
      ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e by
    intro R R₀ _ _ π hπ hnil
    obtain ⟨n, hn⟩ := hnil
    exact key n R R₀ π hπ hn
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn
    refine H R R₀ π hπ ?_
    exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.zero_le 2)).trans hn.le)
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ i hi hX e₀ he₀
    by_cases hn2 : n + 1 ≤ 2
    · exact H R R₀ π hπ (le_bot_iff.mp ((Ideal.pow_le_pow_right hn2).trans hn.le)) X X₀ i hi hX e₀ he₀
    have hn1 : 1 ≤ n := by omega
    set I := RingHom.ker π with hIdef
    set J : Ideal R := I ^ n with hJdef
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self (by omega)
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    let π'' : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π (fun a ha => (RingHom.mem_ker).mp (hJI ha))
    have hcomp : π''.comp q = π := by
      ext a; rfl
    have hsp : spMap π = spMap π'' ≫ spMap q := by
      rw [← hcomp]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have hπ'' : Function.Surjective π'' := Ideal.Quotient.lift_surjective_of_surjective J _ hπ
    have hkerq : RingHom.ker q = J := Ideal.mk_ker
    have hkerπ'' : RingHom.ker π'' = I.map q := by
      have := RingHom.comap_ker π'' q
      rw [hcomp] at this
      rw [← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective (RingHom.ker π''), this]
    have hn'' : RingHom.ker π'' ^ n = ⊥ := by
      rw [hkerπ'', ← Ideal.map_pow]
      exact Ideal.map_quotient_self J
    have hJ2 : RingHom.ker q ^ 2 = ⊥ := by
      rw [hkerq, hJdef, ← pow_mul]
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    let X' : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom (spMap q))
    have hX' : Smooth X'.hom := show Smooth (pullback.snd X.hom (spMap q)) from inferInstance
    have hw : i ≫ X.hom = (X₀.hom ≫ spMap π'') ≫ spMap q := by
      rw [hi.w, hsp, Category.assoc]
    let i' : X₀.left ⟶ X'.left := pullback.lift i (X₀.hom ≫ spMap π'') hw
    have hi'1 : i' ≫ pullback.fst X.hom (spMap q) = i := pullback.lift_fst _ _ _
    have hi'2 : i' ≫ X'.hom = X₀.hom ≫ spMap π'' := pullback.lift_snd _ _ _
    have hi' : IsPullback i' X₀.hom X'.hom (spMap π'') := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom (spMap q)) (h₂₂ := spMap q) (v₁₃ := X.hom) ?_ hi'2
        (IsPullback.of_hasPullback X.hom (spMap q))
      rw [hi'1, ← hsp]
      exact hi
    obtain ⟨e', he'1, he'2⟩ := ih (R ⧸ J) R₀ π'' hπ'' hn'' X' X₀ i' hi' hX' e₀ he₀
    obtain ⟨e, he1, he2⟩ := H R (R ⧸ J) q Ideal.Quotient.mk_surjective hJ2 X X'
      (pullback.fst X.hom (spMap q)) (IsPullback.of_hasPullback X.hom (spMap q)) hX e' he'1
    refine ⟨e, he1, ?_⟩
    calc e₀ ≫ i = e₀ ≫ i' ≫ pullback.fst X.hom (spMap q) := by rw [hi'1]
      _ = (spMap π'' ≫ e') ≫ pullback.fst X.hom (spMap q) := by rw [← Category.assoc, he'2]
      _ = spMap π'' ≫ spMap q ≫ e := by rw [Category.assoc, he2]
      _ = spMap π ≫ e := by rw [hsp, Category.assoc]

end GlobalTheory.SecLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionLiftNilpotentOfSqZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.smooth_section_lift_nilpotent_of_sqZero : (∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e) →
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  first | exact @GlobalTheory.SecLift.lift_of_nilpotent_of_sqZero | exact GlobalTheory.SecLift.lift_of_nilpotent_of_sqZero | (intros; apply GlobalTheory.SecLift.lift_of_nilpotent_of_sqZero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLift

theorem exists_section_lift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  refine GlobalTheory.T.smooth_section_lift_nilpotent_of_sqZero ?_
  intro R R₀ _ _ π hπ hsq X X₀ i hpb hsm e₀ he₀
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hsq]; rfl⟩
  let g₀ := e₀ ≫ i
  have hg₀ : g₀ ≫ X.hom = spMap π := by
    simp only [g₀, Category.assoc]; rw [hpb.w, ← Category.assoc, he₀, Category.id_comp]
  let J : Set R := {h | ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ h V}
  have hS2 := GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine R R₀ π hπ hnil X hsm g₀ hg₀
  have hspan : Ideal.span J = ⊤ := by
    by_contra hne
    obtain ⟨N, hN, hJN⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, hfJ⟩ := hS2 ⟨N, hN.isPrime⟩
    exact hf (hJN (Ideal.subset_span hfJ))
  obtain ⟨s, hsJ, hs⟩ := (Ideal.span_eq_top_iff_finite J).1 hspan
  have hV : ∀ k : s, ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ k.1 V := fun k => hsJ k.2
  choose V hVa hVl using hV
  obtain ⟨e, he1, he2⟩ :=
    GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero R R₀ π hπ hsq X hsm g₀ hg₀ s (fun k => k.1) (by simpa using hs) V hVa hVl
  exact ⟨e, he1, he2.symm⟩

end GlobalTheory.SecLift
end
end
