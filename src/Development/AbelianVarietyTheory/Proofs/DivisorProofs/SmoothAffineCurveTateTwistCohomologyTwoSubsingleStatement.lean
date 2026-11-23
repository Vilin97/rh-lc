module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinementStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomologyStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPowStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFuncStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekindStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNbhdKillingCurveCohomologyClass

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CurveNbhdExcision

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := RingHom.ext fun _ => Subsingleton.elim _ _
  have key : ∀ z : Ht q (sp Z) n i, z = 0 := by
    intro z
    obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q Z Z n i).2 (z, 0)
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1, ← hy.2, hfs]
  rw [key a, key b]

theorem away_zero_subsingleton (B : Type) [CommRing B] : Subsingleton (Localization.Away (0 : B)) := by
  have h : IsUnit (algebraMap B (Localization.Away (0 : B)) 0) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_zero, isUnit_zero_iff] at h
  exact subsingleton_of_zero_eq_one h

theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf n i hn x
  by_cases hu : IsUnit f
  · haveI := away_zero_subsingleton B
    refine ⟨Localization.Away (0 : B), inferInstance, inferInstance, ⟨Algebra.Etale.of_isLocalizationAway 0, ?_, ?_⟩, ?_⟩
    · intro a'
      exact ⟨0, by rw [Subsingleton.elim (a' - _) 0]; exact Ideal.zero_mem _⟩
    · intro a _
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact Submodule.mem_top
    · haveI := ht_subsingleton_of_subsingleton q (Localization.Away (0 : B)) n i
      exact Subsingleton.elim _ _
  · obtain ⟨A', i1, i2, i3, hN, hx⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf hu n i (by omega) x
    exact ⟨A', i1, i2, ⟨i3, hN.1, hN.2⟩, hx⟩

end GlobalTheory.EtC.CurveNbhdExcision
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNbhdKillingCurveCohomologyClassStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.CurveNbhdExcision.main) | (exact GlobalTheory.EtC.CurveNbhdExcision.main) | (intros; apply GlobalTheory.EtC.CurveNbhdExcision.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassAgreeingNearZeros

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.KummerStep

noncomputable abbrev gU (A : Type) [CommRing A] : Aˣ →* (Γ(Spec (CommRingCat.of A), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isUnit_natCast_of {k R : Type} [Field k] [CommRing R] (φ : k →+* R) {q : ℕ} (hq : IsUnit (q : k)) :
    IsUnit (q : R) := by
  simpa using hq.map φ

theorem kum_spMap (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hq : IsUnit (q : A))
    (u : Aˣ) : pull _ (spMap φ) _ _ (kum q (gU A u)) = kum q (gU B (Units.map φ.toMonoidHom u)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [(GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.2.2 (Spec.map (CommRingCat.ofHom φ)) (gU A u) hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 : (Spec.map (CommRingCat.ofHom φ)).appTop = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← h]; simp
  simp only [gU, Units.coe_map, MonoidHom.coe_coe]
  rw [h2]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  simp

theorem kum_pow_eq (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (u v : Aˣ) :
    kum q (gU A (u * v ^ q)) = kum q (gU A u) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [map_mul, map_pow, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A u) _ hq').1, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A v) (gU A v) hq').2, add_zero]

theorem kum_pow (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (v : Aˣ) :
    kum q (gU A (v ^ q)) = 0 := by
  have := kum_pow_eq q hq 1 v
  rw [one_mul] at this
  rw [this, map_one]
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have h := ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hq').1
  rw [one_mul] at h
  simpa using h

theorem of_steps (L1 : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c) (L2 : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q) : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  intro q _ k B _ _ _ _ _ _ hq f hf A' _ _ hA' w
  obtain ⟨A₂, _, _, _, _, hA₂, c, hc⟩ := L1 q k B hq f hf A' hA' w
  set c₀ : (Localization.Away (algebraMap B A₂ f))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (algebraMap B A₂ f)))).hom.hom.toMonoidHom c with hc₀
  have hcc : gU _ c₀ = c := by
    ext; simp [c₀, gU]
  obtain ⟨g, hfg, u, ⟨A₃, _, _, _, _, hA₃, hg, v, hv⟩, C, _, _, hC, v', hv'⟩ := L2 q k B hq f hf A₂ hA₂ c₀
  letI : Algebra A' A₃ := ((algebraMap A₂ A₃).comp (algebraMap A' A₂)).toAlgebra
  haveI : IsScalarTower B A' A₃ := IsScalarTower.of_algebraMap_eq (fun b => by
    show algebraMap B A₃ b = algebraMap A₂ A₃ (algebraMap A' A₂ (algebraMap B A' b))
    rw [← IsScalarTower.algebraMap_apply B A' A₂, ← IsScalarTower.algebraMap_apply B A₂ A₃])
  have hkB : ∀ (R : Type) [CommRing R] [Algebra B R], IsUnit (q : R) := fun R _ _ =>
    isUnit_natCast_of ((algebraMap B R).comp (algebraMap k B)) hq
  refine ⟨g, hfg, A₃, C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hA₃, hg, hC, kum q (gU _ u), ?_, ?_⟩
  · rw [kum_spMap q _ (hkB _)]
    have : Units.map (Localization.awayMap (algebraMap B C) (f * g)).toMonoidHom u = v' ^ q := by
      ext; simpa using hv'
    rw [this]
    exact kum_pow q (hkB _) v'
  · intro φ ψ hφ hψ
    have hu₁ : IsUnit (((algebraMap A₂ (Localization.Away (algebraMap B A₂ f))).comp (algebraMap A' A₂))
        (algebraMap B A' f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hu₂ : IsUnit (((algebraMap A₃ (Localization.Away (algebraMap B A₃ f))).comp (algebraMap A₂ A₃))
        (algebraMap B A₂ f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A₂ A₃]
      exact IsLocalization.Away.algebraMap_isUnit _
    set φ₁ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f) :=
      IsLocalization.Away.lift (algebraMap B A' f) hu₁
    set φ₂ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f) :=
      IsLocalization.Away.lift (algebraMap B A₂ f) hu₂
    have hφ₁ : φ₁.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A' f)) (algebraMap B A' f) hu₁
    have hφ₂ : φ₂.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) hu₂
    have hφe : φ = φ₂.comp φ₁ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) ?_
      rw [hφ, RingHom.comp_assoc, hφ₁, ← RingHom.comp_assoc, hφ₂, RingHom.comp_assoc]
      rfl
    have key := hv φ₂ ψ hφ₂ hψ
    have hkey : Units.map φ₂.toMonoidHom c₀ = Units.map ψ.toMonoidHom u * v ^ q := by
      ext; simpa using key
    rw [hφe, spMap_comp', pull_comp, hc φ₁ hφ₁, ← hcc, kum_spMap q φ₂ (hkB _), hkey, kum_pow_eq q (hkB _),
      kum_spMap q ψ (hkB _)]

theorem exists_class_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a :=
  of_steps GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow

end GlobalTheory.EtC.KummerStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassAgreeingNearZerosStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_kummerClass_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  first | (exact @GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros) | (exact GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros) | (intros; apply GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOp

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_degreeTwo_class_dies_on_principalOpen : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) →
    ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧
      pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq i x
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · have hSH : SH B := GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB
    haveI : Subsingleton (Ht q (sp B) 2 i) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B hSH (tw q i) 2 (by norm_num)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Subsingleton.elim x 0, map_zero]
  · obtain ⟨inst, halg⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    letI := inst
    haveI := halg
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    haveI : Subsingleton (Ht q (sp (FractionRing B)) 2 i) :=
      GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK 2 i le_rfl
    obtain ⟨f, hf, -, hx⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB 2 i x (Subsingleton.elim _ _)
    exact ⟨f, hf, hx⟩

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOpStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (exact GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologyTwoSubsingle

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_tateTwistCohomology_two_subsingleton : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ,
    Subsingleton (Ht q (sp B) 2 i) := by
  intro q _ k B _ _ _ _ _ _ hq i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)).ne'
  have hζ : ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨algebraMap k B z, ?_⟩
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic,
      hz.eq_zero, map_zero]
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q B hqB hζ 2 i 1
  have h0 : ∀ x : Ht q (sp B) 2 1, x = 0 := by
    intro x
    obtain ⟨f, hf, hxf⟩ := GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two q k B hq 1 x
    obtain ⟨A', _, _, hA', hxA'⟩ := GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass q k B hq f hf 2 1 (by norm_num) x
    obtain ⟨w, hw⟩ := GlobalTheory.T.etaleExcision_vanishing_under_refinement q B A' f hA' 1 1 x hxf hxA'
    obtain ⟨g, hfg, A₂, C, _, _, _, _, _, _, h2, hg, hC, a, haC, hwa⟩ := GlobalTheory.T.exists_kummerClass_agreeing_near_zeros q k B hq f hf A' hA' w
    exact hw g hfg A₂ C h2 hg hC a haC hwa
  exact ⟨fun a b => e.injective (by rw [h0 (e a), h0 (e b)])⟩

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologyTwoSubsingleStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ, Subsingleton (Ht q (sp B) 2 i) := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (exact GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton <;> assumption)
end
end
