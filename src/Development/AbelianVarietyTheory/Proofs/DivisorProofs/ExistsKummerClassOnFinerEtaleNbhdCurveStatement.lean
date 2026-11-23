module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonPicEtaleLocalizationUnitsModuloStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyClassDiesOnLocalizationAwayStatement
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitMod

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away_of_isUnit_mod : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B),
    IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) →
    IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  intro B A' _ _ _ f s hA hs
  obtain ⟨hEt, h2, h3⟩ := hA
  obtain ⟨σ, hσ⟩ : ∃ σ : A', σ = algebraMap B A' s := ⟨_, rfl⟩
  rw [← hσ]

  obtain ⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ Ideal.span {f} := by
    obtain ⟨v, hv⟩ := hs.exists_right_inv
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  have hpow : ∀ n : ℕ, (s * t) ^ n - 1 ∈ Ideal.span {f} := by
    intro n
    obtain ⟨c, hc⟩ := (sub_dvd_pow_sub_pow (s * t) 1 n)
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ ht
  haveI : Algebra.Etale A' (Localization.Away σ) := Algebra.Etale.of_isLocalizationAway σ
  haveI : Algebra.Etale B (Localization.Away σ) := Algebra.Etale.comp B A' (Localization.Away σ)
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a', m⟩, hx⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) x
    have hxs : x * algebraMap A' (Localization.Away σ) m = algebraMap A' _ a' := by
      rw [← hx]; exact IsLocalization.mk'_spec _ _ _
    obtain ⟨n, hn⟩ := m.2
    rw [← hn] at hxs
    obtain ⟨b, hb⟩ := h2 (a' * algebraMap B A' t ^ n)
    refine ⟨b, ?_⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hpow n)
    have hc' := congrArg (algebraMap A' (Localization.Away σ)) hc
    have hv' := congrArg (algebraMap A' (Localization.Away σ)) (congrArg (algebraMap B A') hv)
    rw [Ideal.mem_span_singleton']
    refine ⟨-(x * algebraMap A' _ (algebraMap B A' v)) + algebraMap A' _ c, ?_⟩
    simp only [IsScalarTower.algebraMap_apply B A' (Localization.Away σ), map_mul, map_sub, map_pow, map_one,
      ← hσ] at hxs hc' hv' ⊢
    linear_combination hc' - x * hv' - (algebraMap A' (Localization.Away σ) (algebraMap B A' t)) ^ n * hxs
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨⟨c, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) y
    have hys := IsLocalization.mk'_spec (Localization.Away σ) c (⟨σ ^ n, n, rfl⟩ : Submonoid.powers σ)
    have key : algebraMap A' (Localization.Away σ) (algebraMap B A' a * σ ^ n) =
        algebraMap A' (Localization.Away σ) (c * algebraMap B A' f) := by
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hy]
      simp only at hys
      rw [← hys]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers σ) _).1 key
    have hmem : algebraMap B A' (s ^ (k + n) * a) ∈ Ideal.span {algebraMap B A' f} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨σ ^ k * c, ?_⟩
      simp only at hk
      rw [map_mul, map_pow, ← hσ, pow_add]
      linear_combination -hk
    have h1 := h3 _ hmem
    have h4 := hpow (k + n)
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h4
    rw [Ideal.mem_span_singleton']
    refine ⟨t ^ (k + n) * p - a * q, ?_⟩
    linear_combination t ^ (k + n) * hp - a * hq

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitModStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B), IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) → IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (exact GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationDescendAway

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem units_localization_descend_away (A : Type) [CommRing A] (M : Submonoid A)
    (u : (Localization M)ˣ) :
    ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M,
      φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  obtain ⟨⟨a, m₁⟩, ha⟩ := IsLocalization.mk'_surjective M (u : Localization M)
  obtain ⟨⟨b, m₂⟩, hb⟩ := IsLocalization.mk'_surjective M ((u⁻¹ : (Localization M)ˣ) : Localization M)
  simp only at ha hb
  have hprod : IsLocalization.mk' (Localization M) (a * b) (m₁ * m₂) = 1 := by
    rw [IsLocalization.mk'_mul, ha, hb]; simp
  have h1 : algebraMap A (Localization M) (a * b) = algebraMap A (Localization M) ((m₁ * m₂ : M) : A) := by
    have := IsLocalization.mk'_spec (Localization M) (a * b) (m₁ * m₂)
    rw [hprod, one_mul] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
  set m : A := (m₁ : A) * m₂ * c with hm
  have hmM : m ∈ M := M.mul_mem (M.mul_mem m₁.2 m₂.2) c.2
  have hc' : (c : A) * (a * b) = (c : A) * ((m₁ : A) * m₂) := by
    simpa [Submonoid.coe_mul] using hc
  let s := IsLocalization.Away.invSelf (S := Localization.Away m) m
  have hs : algebraMap A (Localization.Away m) m * s = 1 := IsLocalization.Away.mul_invSelf m
  let x : Localization.Away m := algebraMap A _ (a * (m₂ * c)) * s
  let y : Localization.Away m := algebraMap A _ (b * (m₁ * c)) * s
  have hxy : x * y = 1 := by
    have e : a * (m₂ * c) * (b * (m₁ * c)) = m * m := by
      rw [hm]; linear_combination ((m₁ : A) * m₂ * c) * hc'
    calc x * y = algebraMap A _ (a * (m₂ * c) * (b * (m₁ * c))) * s * s := by
          simp only [x, y, map_mul]; ring
      _ = (algebraMap A (Localization.Away m) m * s) * (algebraMap A (Localization.Away m) m * s) := by
          rw [e, map_mul]; ring
      _ = 1 := by rw [hs, one_mul]
  refine ⟨m, hmM, ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  intro φ hφ
  have hφa : ∀ r : A, φ (algebraMap A _ r) = algebraMap A (Localization M) r := fun r =>
    congrArg (fun f : A →+* Localization M => f r) hφ
  apply Units.ext
  show φ x = (u : Localization M)
  have hu : (u : Localization M) * algebraMap A _ (m₁ : A) = algebraMap A _ a := by
    rw [← ha]; exact IsLocalization.mk'_spec _ _ _
  have hφs : algebraMap A (Localization M) m * φ s = 1 := by
    rw [← hφa, ← map_mul, hs, map_one]
  have hx : φ x * algebraMap A (Localization M) (m₁ : A) = algebraMap A _ a := by
    have : φ x * algebraMap A (Localization M) (m₁ : A)
        = algebraMap A (Localization M) a * (algebraMap A (Localization M) m * φ s) := by
      simp only [x, map_mul, hφa, hm]; ring
    rw [this, hφs, mul_one]
  have hunit : IsUnit (algebraMap A (Localization M) (m₁ : A)) := IsLocalization.map_units _ m₁
  exact hunit.mul_left_inj.1 (hx.trans hu.symm)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationDescendAwayStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_away_unit_map_eq : ∀ (A : Type) [CommRing A] (M : Submonoid A) (u : (Localization M)ˣ), ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  first | (exact @GlobalTheory.units_localization_descend_away) | (exact GlobalTheory.units_localization_descend_away) | (intros; apply GlobalTheory.units_localization_descend_away <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurve

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KummerLoc

noncomputable abbrev gU (R : Type) [CommRing R] : Rˣ →* (Γ(Spec (CommRingCat.of R), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom

theorem pull_spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    {q : ℕ} {n i : ℤ} (x : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp φ)) _ _ x = pull _ (spMap ψ) _ _ (pull _ (spMap φ) _ _ x) := by
  rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp]; rfl

theorem pull_kum_gU (hnat : DivisorNaturality) (q : ℕ) [NeZero q] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hq : IsUnit (q : R)) (v : Rˣ) :
    pull _ (spMap φ) _ _ (kum q (gU R v)) = kum q (gU S (Units.map φ.toMonoidHom v)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rw [(hnat q).2.2.2 _ _ hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom (v : R)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simpa using h2.symm



theorem exists_kummer_on_finer_nbhd : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  intro q _ k B _ _ _ _ _ _ hq f _ A' _ _ hA' w
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hqA : IsUnit (q : A') := by simpa using hqB.map (algebraMap B A')
  haveI : Algebra.Etale B A' := hA'.1
  set SB : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
    (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hSB
  set M : Submonoid A' := Algebra.algebraMapSubmonoid A' SB with hM
  have hfM : (algebraMap B A' f) ∈ M := ⟨f, Submonoid.mem_sup_right (Submonoid.mem_powers f), rfl⟩
  let φf : Localization.Away (algebraMap B A' f) →+* Localization M :=
    IsLocalization.Away.lift (algebraMap B A' f) (IsLocalization.map_units (Localization M) (⟨(algebraMap B A' f), hfM⟩ : M))
  have hφf : φf.comp (algebraMap A' _) = algebraMap A' (Localization M) := IsLocalization.Away.lift_comp _ _
  haveI := GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo B f A'
  have hqL : IsUnit (q : Localization M) := by simpa using hqA.map (algebraMap A' (Localization M))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (Localization M) hqL (fun c _ => Subsingleton.elim _ _) (pull _ (spMap φf) _ _ w)
  let u₀ : (Localization M)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization M))).hom.hom.toMonoidHom u
  have hu₀ : gU _ u₀ = u := by ext; simp [u₀]
  obtain ⟨m₀, hm₀, v, hv⟩ := GlobalTheory.T.exists_away_unit_map_eq A' M u₀
  have hm₁ : (algebraMap B A' f) * m₀ ∈ M := M.mul_mem hfM hm₀
  have hunit1 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀)) ((algebraMap B A' f) * m₀)) := IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (algebraMap B A' f) →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift (algebraMap B A' f) (isUnit_of_mul_isUnit_left (by simpa using hunit1))
  let β : Localization.Away m₀ →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift m₀ (isUnit_of_mul_isUnit_right (by simpa using hunit1))
  let φ₁ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization M :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (IsLocalization.map_units (Localization M) (⟨_, hm₁⟩ : M))
  have hα : α.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hβ : β.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hφ₁ : φ₁.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₀ : IsUnit (q : Localization.Away m₀) := by simpa using hqA.map (algebraMap A' _)
  have hqm₁ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀)) := by simpa using hqA.map (algebraMap A' _)
  have hnat := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  set y := pull _ (spMap α) _ _ w - kum q (gU _ (Units.map β.toMonoidHom v)) with hy
  have hy0 : pull _ (spMap φ₁) _ _ y = 0 := by
    rw [hy, map_sub, ← pull_spMap_comp, pull_kum_gU hnat q _ hqm₁]
    have e1 : φ₁.comp α = φf := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) (by rw [RingHom.comp_assoc, hα, hφ₁, hφf])
    have e2 : Units.map φ₁.toMonoidHom (Units.map β.toMonoidHom v) = u₀ := by
      rw [← hv (φ₁.comp β) (by rw [RingHom.comp_assoc, hβ, hφ₁])]; ext; rfl
    rw [e1, e2, hu₀, hu, sub_self]
  obtain ⟨m', hm', hψ⟩ := GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q A' M 1 1 hqA ((algebraMap B A' f) * m₀) hm₁ y φ₁ hφ₁ hy0
  obtain ⟨b, hb, hbm⟩ := M.mul_mem hm₁ hm'
  obtain ⟨s, hs, t, ht, rfl⟩ := Submonoid.mem_sup.1 hb
  obtain ⟨n, rfl⟩ := ht
  have hs' : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) := hs
  refine ⟨Localization.Away (algebraMap B A' s), inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' B A' f s hA' hs', ?_⟩
  set A₂ := Localization.Away (algebraMap B A' s)
  set g : A' →+* Localization.Away (algebraMap B A₂ f) := (algebraMap A₂ _).comp (algebraMap A' A₂) with hg
  have hgu : IsUnit (g ((algebraMap B A' f) * m₀ * m')) := by
    rw [← hbm]
    simp only [map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · exact (IsLocalization.Away.algebraMap_isUnit (algebraMap B A' s)).map (algebraMap A₂ _)
    · have : g (algebraMap B A' f) = algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) := by
        rw [hg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂ f]
      rw [this]
      exact IsLocalization.Away.algebraMap_isUnit _
  let χ : Localization.Away ((algebraMap B A' f) * m₀ * m') →+* Localization.Away (algebraMap B A₂ f) :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀ * m') hgu
  have hχ : χ.comp (algebraMap A' _) = g := IsLocalization.Away.lift_comp _ _
  have hunit2 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀ * m')) ((algebraMap B A' f) * m₀ * m')) :=
    IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization.Away ((algebraMap B A' f) * m₀ * m') :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (isUnit_of_mul_isUnit_left (by simpa using hunit2))
  have hψc : ψ.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₂ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀ * m')) := by simpa using hqA.map (algebraMap A' _)
  clear_value χ ψ β α
  refine ⟨gU _ (Units.map (χ.comp (ψ.comp β)).toMonoidHom v), fun φ hφ => ?_⟩
  have e3 : φ = χ.comp (ψ.comp α) := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f))
    (by rw [hφ, RingHom.comp_assoc, RingHom.comp_assoc, hα, hψc, hχ])
  have hw : pull _ (spMap α) _ _ w = y + kum q (gU _ (Units.map β.toMonoidHom v)) := by
    rw [hy, sub_add_cancel]
  subst e3
  rw [pull_spMap_comp, pull_spMap_comp, hw]
  have hψy := hψ ψ hψc
  rw [map_add (pull _ (spMap ψ) _ _)]
  rw [hψy, zero_add]
  rw [pull_kum_gU hnat q ψ hqm₁]
  have key : pull _ (spMap χ) _ _ (kum q (gU _ (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) =
      kum q (gU _ (Units.map χ.toMonoidHom (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) :=
    pull_kum_gU hnat q χ hqm₂ _
  refine key.trans ?_
  exact congrArg (kum q) (congrArg (gU _) (Units.ext rfl))

end GlobalTheory.EtC.KummerLoc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurveStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  first | (exact @GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (exact GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (intros; apply GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd <;> assumption)
end
end
