module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExcisionNbhdAdjoinRootStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdTransStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitFormLocalizationEtaleNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDivisorUnitDecompositionStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPowerOnExcisionNeighbourhood

section

@[expose] public section

open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_isPow_on_excisionNbhd : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro k B _ _ _ _ _ _ q hq f g hg u t n' d' hn hd hu
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨a, bn, ha⟩ := hn
  obtain ⟨a', bd, hb⟩ := hd
  have hw : (a * a' * g - a - a') * g = n' * d' * (bn * bd) - 1 := by
    linear_combination (-(bd * d')) * ha + (a * g - 1) * hb
  have hC' : IsExcisionNbhd B (Localization.Away (n' * d')) g :=
    GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B B g (isExcisionNbhd_self B g) (n' * d') (bn * bd)
      (Ideal.mem_span_singleton'.mpr ⟨_, hw⟩)
  set C' := Localization.Away (n' * d') with hC'def
  have hnd : IsUnit (algebraMap B C' (n' * d')) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hnd
  have hnC : IsUnit (algebraMap B C' n') := isUnit_of_mul_isUnit_left hnd
  have hdC : IsUnit (algebraMap B C' d') := isUnit_of_mul_isUnit_right hnd
  set Di : C' := ((hdC.unit⁻¹ : C'ˣ) : C') with hDi
  have hDi1 : Di * algebraMap B C' d' = 1 := by rw [hDi]; exact hdC.val_inv_mul
  set ε : C' := algebraMap B C' n' * Di with hεdef
  have hε : IsUnit ε := hnC.mul (Units.isUnit _)
  have hεd : ε * algebraMap B C' d' = algebraMap B C' n' := by rw [hεdef, mul_assoc, hDi1, mul_one]
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B q hq g hg (n' * bd) (bn * d')
    (Ideal.mem_span_singleton'.mpr ⟨a * a' * g - a - a', by linear_combination hw⟩)
  obtain ⟨w, hw'⟩ := Ideal.mem_span_singleton'.mp hr
  have hqC : IsUnit (q : C') := by simpa using hq.map ((algebraMap B C').comp (algebraMap k B))
  have hεr : ε - algebraMap B C' r ^ q ∈ Ideal.span {algebraMap B C' g} := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap B C' n' * Di * algebraMap B C' a' + algebraMap B C' w, ?_⟩
    have e1 := congrArg (algebraMap B C') hw'
    have e2 := congrArg (algebraMap B C') hb
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_one] at e1 e2
    rw [hεdef]
    linear_combination e1 + (algebraMap B C' n' * Di) * e2 - (algebraMap B C' n' * algebraMap B C' bd) * hDi1
  obtain ⟨C, _, _, hC, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit C' (algebraMap B C' g) q hqC ε (algebraMap B C' r) hε hεr
  letI : Algebra B C := ((algebraMap C' C).comp (algebraMap B C')).toAlgebra
  haveI : IsScalarTower B C' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨C, inferInstance, inferInstance, GlobalTheory.T.isExcisionNbhd_trans' B C' C g hC' hC, ?_⟩
  set L := Localization.Away (algebraMap B C (f * g))
  set ψ : B →+* L := (algebraMap C L).comp (algebraMap B C) with hψ
  set ρ : C' →+* L := (algebraMap C L).comp (algebraMap C' C) with hρ
  have hψρ : ∀ y : B, ψ y = ρ (algebraMap B C' y) := fun _ => rfl
  have hφ : ∀ y : B, Localization.awayMap (algebraMap B C) (f * g)
      (algebraMap B (Localization.Away (f * g)) y) = ψ y := by
    intro y; exact IsLocalization.map_eq _ _
  have hu' : Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d') = ψ n' := by
    have h := congrArg (Localization.awayMap (algebraMap B C) (f * g)) hu
    rw [map_mul (Localization.awayMap (algebraMap B C) (f * g)), hφ, hφ] at h
    rw [← map_pow ψ, ← map_mul ψ]; exact h
  have hnL : IsUnit (ψ n') := by rw [hψρ]; exact hnC.map ρ
  have hdL : IsUnit (ψ d') := by rw [hψρ]; exact hdC.map ρ
  have hεL : ρ ε * ψ d' = ψ n' := by
    have := congrArg ρ hεd; rw [map_mul] at this; rw [hψρ, hψρ]; exact this
  have hxL : algebraMap C L x ^ q = ρ ε := by
    have := congrArg (algebraMap C L) hx; rw [map_pow] at this; exact this.symm
  have hXU : algebraMap C L x ^ q = Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * ψ t ^ q := by
    rw [← hdL.mul_left_inj, hxL, hεL, ← hu', mul_assoc]
  have hTq : IsUnit (ψ t ^ q) := by
    have h : IsUnit (Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d')) := by
      rw [hu']; exact hnL
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)
  have hT : IsUnit (ψ t) := (isUnit_pow_iff hq0).mp hTq
  have hX : IsUnit (algebraMap C L x) := by
    refine (isUnit_pow_iff hq0).mp ?_
    rw [hXU]; exact ((Units.map (Localization.awayMap (algebraMap B C) (f * g) : Localization.Away (f * g) →* L)) u).isUnit.mul hTq
  refine ⟨hX.unit * hT.unit⁻¹, ?_⟩
  rw [Units.val_mul, mul_pow, IsUnit.unit_spec, hXU, mul_assoc, ← mul_pow, hT.mul_val_inv, one_pow, mul_one]

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeUnitEtaleExtension

section

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.coprime_unit_etale_extension : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (exact GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (intros; apply GlobalTheory.EtC.unit_isPow_on_excisionNbhd  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitFormLocalizationEtaleNbhdStatement

section

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_unit_form_localization_etale_nbhd : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂] [Algebra B A₂] (f : B), IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧ algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  first | (exact @GlobalTheory.DivUnitForm.unit_form) | (exact GlobalTheory.DivUnitForm.unit_form) | (intros; apply GlobalTheory.DivUnitForm.unit_form  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqMulPowOnEtaleExcisionNbhdZeroLocus

section

@[expose] public section

open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_eq_mul_qth_power_near_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  intro k B _ _ _ _ _ _ q hq f hf A₂ _ _ hA₂ c b₁ m e he hc g hg u n d hn hd hu
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x₁, y₁, hxy₁⟩ := (hg.mul_right hn).mul_right hd
  obtain ⟨a, ha⟩ : ∃ a : A₂, a = algebraMap B A₂ (g * n * d) * e := ⟨_, rfl⟩
  have hab : a * algebraMap B A₂ y₁ - 1 ∈ Ideal.span {algebraMap B A₂ f} := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp he
    have h1 := congrArg (algebraMap B A₂) hxy₁
    simp only [map_add (f := _), map_mul, map_one] at h1
    rw [Ideal.mem_span_singleton, ha]
    refine ⟨-(algebraMap B A₂ x₁) * e + t, ?_⟩
    simp only [map_mul]
    linear_combination e * h1 + ht
  have hA₂' : IsExcisionNbhd B (Localization.Away a) f := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA₂ a (algebraMap B A₂ y₁) hab
  have hdvd : ∀ z : A₂, z ∣ a → IsUnit (algebraMap A₂ (Localization.Away a) z) := fun z hz =>
    isUnit_of_dvd_unit (map_dvd _ hz) (IsLocalization.Away.algebraMap_isUnit a)
  have hgu := hdvd (algebraMap B A₂ g) ⟨algebraMap B A₂ n * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hnu := hdvd (algebraMap B A₂ n) ⟨algebraMap B A₂ g * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hdu := hdvd (algebraMap B A₂ d) ⟨algebraMap B A₂ g * algebraMap B A₂ n * e, by rw [ha]; simp only [map_mul]; ring⟩
  have heu := hdvd e ⟨algebraMap B A₂ (g * n * d), by rw [ha]; ring⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : A₂, ε₀ = algebraMap B A₂ n * (algebraMap B A₂ d * e) ^ j := ⟨_, rfl⟩
  have hεu : IsUnit (algebraMap A₂ (Localization.Away a) ε₀) := by
    rw [hε₀, map_mul, map_pow, map_mul]; exact hnu.mul ((hdu.mul heu).pow j)
  obtain ⟨x₂, y₂, h₂⟩ := hn.mul_right (hd.pow_right (n := j))
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B (j + 1) hq f hf (n * d ^ j) y₂
    (Ideal.mem_span_singleton.mpr ⟨-x₂, by linear_combination h₂⟩)
  have hcong : ε₀ - algebraMap B A₂ r ^ (j + 1) ∈ Ideal.span {algebraMap B A₂ f} := by
    have h1 : algebraMap B A₂ f ∣ algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) :=
      map_dvd _ (Ideal.mem_span_singleton.mp hr)
    have h2 : algebraMap B A₂ f ∣ e ^ j - 1 :=
      (Ideal.mem_span_singleton.mp he).trans (by simpa using sub_dvd_pow_sub_pow e 1 j)
    have h3 : ε₀ - algebraMap B A₂ r ^ (j + 1) = algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) +
        algebraMap B A₂ n * algebraMap B A₂ d ^ j * (e ^ j - 1) := by
      rw [hε₀]; simp only [map_sub, map_mul, map_pow]; ring
    rw [Ideal.mem_span_singleton, h3]; exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  have hcong' : algebraMap A₂ (Localization.Away a) ε₀ - algebraMap B (Localization.Away a) r ^ (j + 1) ∈
      Ideal.span {algebraMap B (Localization.Away a) f} := by
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) r,
      IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) f, ← map_pow, ← map_sub,
      Ideal.mem_span_singleton]
    exact map_dvd _ (Ideal.mem_span_singleton.mp hcong)
  have hqu : IsUnit ((j + 1 : ℕ) : Localization.Away a) := by
    have := hq.map ((algebraMap B (Localization.Away a)).comp (algebraMap k B)); rwa [map_natCast] at this
  obtain ⟨A₃, _, _, hA₃, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit (Localization.Away a) (algebraMap B (Localization.Away a) f)
    (j + 1) hqu _ _ hεu hcong'
  letI : Algebra B A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap B (Localization.Away a)))
  letI : Algebra A₂ A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap A₂ (Localization.Away a)))
  haveI t1 : IsScalarTower B (Localization.Away a) A₃ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t3 : IsScalarTower B A₂ A₃ := IsScalarTower.of_algebraMap_eq (fun z => by
    show algebraMap (Localization.Away a) A₃ (algebraMap B (Localization.Away a) z) =
      algebraMap (Localization.Away a) A₃ (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ z))
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) z])
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, t3, GlobalTheory.T.isExcisionNbhd_trans' B (Localization.Away a) A₃ f hA₂' hA₃, ?_, ?_⟩
  · have : algebraMap B A₃ g = algebraMap (Localization.Away a) A₃
        (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ g)) := by
      rw [← IsScalarTower.algebraMap_apply B A₂ (Localization.Away a)]; rfl
    rw [this]; exact hgu.map _
  have hDu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f))
      (algebraMap A₂ A₃ (algebraMap B A₂ d * e))) := by
    have hde : IsUnit (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ d * e)) := by
      rw [map_mul]; exact hdu.mul heu
    exact (hde.map (algebraMap (Localization.Away a) A₃)).map _
  have hX : algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x ^ (j + 1) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) *
      (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
       algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j := by
    rw [← map_pow, ← hx]
    show algebraMap A₃ _ (algebraMap A₂ A₃ ε₀) = _
    rw [hε₀]; simp only [map_mul, map_pow]
  have hXu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x) :=
    (isUnit_pow_iff (Nat.succ_ne_zero j)).mp (by rw [← map_pow, ← hx]; exact (hεu.map _).map _)
  have hFu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ f))) := by
    rw [← IsScalarTower.algebraMap_apply B A₂ A₃]; exact IsLocalization.Away.algebraMap_isUnit _
  refine ⟨hXu.unit * hDu.unit⁻¹, fun φ ψ hφ hψ => ?_⟩
  have hφ' : ∀ y, φ (algebraMap A₂ _ y) = algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ y) :=
    fun y => RingHom.congr_fun hφ y
  have hψ' : ∀ z, ψ (algebraMap B _ z) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ z)) := fun z => by
    have := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply] at this
    rw [this, IsScalarTower.algebraMap_apply B A₂ A₃ z]
  have H1 := congrArg φ hc
  have H2 := congrArg ψ hu
  simp only [map_mul, map_pow, hφ'] at H1
  simp only [map_mul, map_pow, hψ'] at H2
  have hW := hDu.mul_val_inv
  rw [Units.val_mul, IsUnit.unit_spec]
  generalize (↑hDu.unit⁻¹ : Localization.Away (algebraMap B A₃ f)) = W at hW ⊢
  simp only [map_mul] at hW hFu
  have key0 : φ c * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) =
      ψ u * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) := by
    apply (hFu.pow m).mul_right_cancel
    linear_combination -(algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d))) * H1 + H2
  calc φ c = φ c * (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) * W) ^ (j + 1) := by
        rw [hW, one_pow, mul_one]
    _ = _ := by
      linear_combination (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j * W ^ (j + 1) * key0 -
        ψ u * W ^ (j + 1) * hX

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqMulPowOnEtaleExcisionNbhdZeroLocusStatement

section

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus) | (exact GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus) | (intros; apply GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPow

section

@[expose] public section

namespace GlobalTheory.EtC

theorem kummer_divisor_step : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro q k B _ _ _ _ _ _ hq f hf A₂ _ _ hA c
  obtain ⟨b₁, m, e, he, hc⟩ := GlobalTheory.T.exists_unit_form_localization_etale_nbhd B A₂ f hA c
  by_cases hb : b₁ = 0
  · refine ⟨1, isCoprime_one_right, 1, ?_, ⟨B, inferInstance, inferInstance, isExcisionNbhd_self B 1, 1, by simp⟩⟩
    have hL := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA e 1 (by simpa using he)
    refine ⟨Localization.Away e, inferInstance, inferInstance, inferInstance, inferInstance, hL, by simp, 1, ?_⟩
    intro φ ψ hφ hψ
    subst hb
    have hc' := congrArg φ hc
    simp only [map_zero, map_mul, map_pow] at hc'
    have hx : IsUnit (φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) e) *
        φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f)) ^ m) := by
      have h1 : ∀ y : A₂, φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) y) =
          algebraMap (Localization.Away e) _ (algebraMap A₂ (Localization.Away e) y) := fun y => by
        rw [← RingHom.comp_apply, hφ]; rfl
      rw [h1, h1]
      refine IsUnit.mul ((IsLocalization.Away.algebraMap_isUnit e).map _) (IsUnit.pow _ ?_)
      rw [← IsScalarTower.algebraMap_apply]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (Localization.Away e) f)) (algebraMap B (Localization.Away e) f)
    have hu := (c.isUnit.map φ).mul hx
    rw [← hc'] at hu
    haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
    exact Subsingleton.elim _ _
  · obtain ⟨g, hg0, hfg, u, n, d, t, n', d', hn, hd, hn', hd', h1, h2⟩ := GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition k B q hq f hf b₁ hb m
    exact ⟨g, hfg, u, GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus k B q hq f hf A₂ hA c b₁ m e he hc g hfg u n d hn hd h1,
      GlobalTheory.T.coprime_unit_etale_extension k B q hq f g hg0 u t n' d' hn' hd' h2⟩

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPowStatement

section

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.kummer_divisor_step) | (exact GlobalTheory.EtC.kummer_divisor_step) | (intros; apply GlobalTheory.EtC.kummer_divisor_step <;> assumption)
end
end
