module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentFieldStatement
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdAllPowOfFrobeniusEqKilledByPerfectPointsStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixFlatOfTiltMapsAgree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetractStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentOfPointsKilled

section

@[expose] public section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem descent_of_points_killed : ∀ (l : ℕ) [Fact l.Prime] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : A) (pr : B →ₗ[A] A), ((l : ℕ) : B) = 0 → algebraMap A B u ∈ nonZeroDivisors B → IsHausdorff (Ideal.span {algebraMap A B u}) B → ∀ (κ : Type) [Fintype κ] (x : κ → B), (∀ (T : Type) [CommRing T] (i₁ i₂ : B →+* T), (∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a)) → IsUnit (i₁ (algebraMap A B u)) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : B →+* O), ψ (algebraMap A B u) ≠ 0 → ¬ IsUnit (ψ (algebraMap A B u)) → IsAdicComplete (Ideal.span {ψ (algebraMap A B u)}) O → (∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a)) → ∀ j, ψ (x j) = ψ' (x j)) → pr 1 = 1 → ∀ j, x j = algebraMap A B (pr (x j)) := by
  intro l _ A B _ _ _ _ u pr hl hu hH κ _ x hEq hPt hpr
  let iL : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  let U : B ⊗[A] B := algebraMap A (B ⊗[A] B) u
  let D : κ → B ⊗[A] B := fun j => iL (x j) - iR (x j)
  have hiL : ∀ a, iL (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iL.commutes a
  have hiR : ∀ a, iR (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iR.commutes a

  have hlR : ((l : ℕ) : B ⊗[A] B) = 0 := by
    rw [← map_natCast iL, hl, map_zero]

  have hUreg : U ∈ nonZeroDivisors (B ⊗[A] B) := by
    have hinj : Function.Injective (LinearMap.mulLeft A (algebraMap A B u)) := by
      intro b b' hbb
      have h0 : (b - b') * algebraMap A B u = 0 := by
        simp only [LinearMap.mulLeft_apply] at hbb
        rw [sub_mul, mul_comm b, mul_comm b', hbb, sub_self]
      exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hu).mp h0)
    have hinj' := Module.Flat.rTensor_preserves_injective_linearMap (M := B) _ hinj
    have hmul : ∀ y : B ⊗[A] B, y * U = LinearMap.rTensor B (LinearMap.mulLeft A (algebraMap A B u)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b b' =>
        simp [U, Algebra.TensorProduct.algebraMap_apply, mul_comm]
      | add y z hy hz => rw [add_mul, hy, hz, map_add (f := _)]
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    rw [hmul] at hy
    exact hinj' (by rw [hy, map_zero])

  obtain ⟨h, c', hc'⟩ : ∃ (h : ℕ) (c' : κ → κ → B ⊗[A] B), ∀ j, U ^ h * D j = ∑ i, D i ^ l * c' i j := by
    let T := Localization.Away U
    let i₁ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iL.toRingHom
    let i₂ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iR.toRingHom
    have hA : ∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a) := by
      intro a
      simp only [i₁, i₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have hunit : IsUnit (i₁ (algebraMap A B u)) := by
      simp only [i₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL]
      exact IsLocalization.Away.algebraMap_isUnit U
    obtain ⟨c, hc⟩ := hEq T i₁ i₂ hA hunit
    obtain ⟨⟨b, hb⟩, hb'⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers U) (S := T)
      (Finset.univ : Finset (κ × κ)) (fun p => c p.1 p.2)
    obtain ⟨h, rfl⟩ := hb
    choose c' hc'' using fun (p : κ × κ) => hb' p (Finset.mem_univ p)
    refine ⟨h, fun i j => c' (i, j), fun j => ?_⟩
    have hD : ∀ i, algebraMap (B ⊗[A] B) T (D i) = i₁ (x i) - i₂ (x i) := by
      intro i; simp [D, i₁, i₂]
    apply IsLocalization.injective T (M := Submonoid.powers U) (Submonoid.powers_le.mpr hUreg)

    rw [map_mul, map_sum, hD, hc j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, hD]
    rw [hc'' (i, j)]
    change _ = _ * ((U ^ h) • c i j)
    rw [Algebra.smul_def, map_pow]
    ring

  have hkey : ∀ (m : ℕ) j, U ^ m ∣ D j := by
    refine GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (B ⊗[A] B) U hlR hUreg κ D c' h hc' ?_
    intro O _ _ _ _ _ f hf0 hfnu hcomp j
    let ψ : B →+* O := f.comp iL.toRingHom
    let ψ' : B →+* O := f.comp iR.toRingHom
    have hψ : ψ (algebraMap A B u) = f U := by
      simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, U]
    have hagree : ∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a) := by
      intro a
      simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have := hPt O ψ ψ' (by rw [hψ]; exact hf0) (by rw [hψ]; exact hfnu) (by rw [hψ]; exact hcomp) hagree j
    simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    simp only [D, map_sub, this, sub_self]

  let φ : B ⊗[A] B →ₗ[A] B := TensorProduct.lift ((LinearMap.lsmul A B).comp pr)
  have hφ : ∀ b b' : B, φ (b ⊗ₜ b') = pr b • b' := fun b b' => by simp [φ]
  intro j
  have hφD : φ (D j) = algebraMap A B (pr (x j)) - x j := by
    simp only [D, map_sub]
    change φ (x j ⊗ₜ 1) - φ (1 ⊗ₜ x j) = _
    rw [hφ, hφ, hpr, one_smul, Algebra.smul_def, mul_one]
  have hmem : ∀ n : ℕ, algebraMap A B (pr (x j)) - x j ∈ Ideal.span {algebraMap A B u ^ n} := by
    intro n
    obtain ⟨r, hr⟩ := hkey n j
    rw [← hφD, hr]
    have : U ^ n * r = u ^ n • r := by simp [U, Algebra.smul_def, map_pow]
    rw [this, LinearMap.map_smul, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hz := hH.haus (algebraMap A B (pr (x j)) - x j) (fun n => by
    rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
    exact hmem n)
  exact (sub_eq_zero.mp hz).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentOfPointsKilledStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.descent_of_points_killed_alt : ∀ (l : ℕ) [Fact l.Prime] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : A) (pr : B →ₗ[A] A), ((l : ℕ) : B) = 0 → algebraMap A B u ∈ nonZeroDivisors B → IsHausdorff (Ideal.span {algebraMap A B u}) B → ∀ (κ : Type) [Fintype κ] (x : κ → B), (∀ (T : Type) [CommRing T] (i₁ i₂ : B →+* T), (∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a)) → IsUnit (i₁ (algebraMap A B u)) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : B →+* O), ψ (algebraMap A B u) ≠ 0 → ¬ IsUnit (ψ (algebraMap A B u)) → IsAdicComplete (Ideal.span {ψ (algebraMap A B u)}) O → (∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a)) → ∀ j, ψ (x j) = ψ' (x j)) → pr 1 = 1 → ∀ j, x j = algebraMap A B (pr (x j)) := by
  first | exact @GlobalTheory.descent_of_points_killed | exact GlobalTheory.descent_of_points_killed | (intros; apply GlobalTheory.descent_of_points_killed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixFlatOfTiltMapsAgreeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_fixFlat_of_tilt_maps_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ ψ' : OCb l →+* O, (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) → ∃ g : ↥(GK K), bk.FixFlat g ∧ ∀ y, ψ' y = ψ (Per.σF (g : GQ l) y) := by
  first | exact @GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree | exact GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree | (intros; apply GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantMemReductionOfFrobeniusEquation

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.TwoCopy

variable {l : ℕ} [hl : Fact l.Prime]

theorem dvd_pow_of_ne_zero {π b : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (hb : b ≠ 0) :
    ∃ n : ℕ, b ∣ π ^ n := by
  haveI := GlobalTheory.FrobInt.valuationRing_tilt l
  by_contra h
  push_neg at h
  apply hb
  refine hπ.haus b fun n => ?_
  obtain ⟨c, hc⟩ : π ^ n ∣ b := by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond b (π ^ n)
    · exact absurd ⟨c, hc.symm⟩ (h n)
    · exact ⟨c, hc.symm⟩
  rw [SModEq.zero, hc, ← smul_eq_mul]
  exact Submodule.smul_mem_smul (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    Submodule.mem_top

theorem isUnit_of_ne_zero {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) (y : OCb l) (hy : y ≠ 0) : IsUnit (i y) := by
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ hy
  exact isUnit_of_mul_isUnit_left (y := i c) (by rw [← map_mul, ← hc, map_pow]; exact hu.pow n)

theorem exists_ext {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) :
    ∃ j : Cb l →+* T, ∀ y, j (algebraMap (OCb l) (Cb l) y) = i y :=
  ⟨IsLocalization.lift (M := nonZeroDivisors (OCb l)) (S := Cb l) (g := i)
      fun y => isUnit_of_ne_zero hπ i hu y (nonZeroDivisors.ne_zero y.2),
    fun y => IsLocalization.lift_eq _ y⟩

theorem exists_clear {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (x : Cb l) :
    ∃ (n : ℕ) (y : OCb l), algebraMap (OCb l) (Cb l) π ^ n * x = algebraMap (OCb l) (Cb l) y := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (OCb l)) x
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ (nonZeroDivisors.ne_zero b.2)
  refine ⟨n, c * a, ?_⟩
  simp only at h
  rw [← map_pow, hc, map_mul, map_mul, ← h]
  ring

theorem exists_clear_family {κ : Type} [Fintype κ] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (x : κ → Cb l) : ∃ (m : ℕ) (x' : κ → OCb l), ∀ j,
      algebraMap (OCb l) (Cb l) π ^ m * x j = algebraMap (OCb l) (Cb l) (x' j) := by
  choose n y hy using fun j => exists_clear hπ (x j)
  refine ⟨∑ j, n j, fun j => π ^ (∑ i, n i - n j) * y j, fun j => ?_⟩
  have hle : n j ≤ ∑ i, n i := Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)
  rw [map_mul, ← hy j, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem map_constantCoeff_surj {F : Type} [CommRing F] (a : F⟦X⟧) :
    ∃ s : (WittVector l F)⟦X⟧, PowerSeries.map (WittVector.constantCoeff (p := l) (R := F)) s = a :=
  ⟨PowerSeries.mk fun n => WittVector.teichmuller l (PowerSeries.coeff n a), by
    ext n
    simp [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

end GlobalTheory.BSP.TwoCopy

namespace GlobalTheory.BSP.TwoCopy

theorem mem_reduction_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) →
    (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T),
      (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) →
    ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk κ _ x hfix hφ
  obtain ⟨ek, prA, hek, hinj, hpr, hpr1⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨hoe, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨-, -, -, h0, -, hc, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  have hH : IsHausdorff (Ideal.span {bk.flat}) (OCb l) := hc.toIsHausdorff
  have hX : ek X = bk.flat := by
    have := hek X
    rwa [PowerSeries.map_X, bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  obtain ⟨m, x', hx'⟩ := exists_clear_family hH x
  letI : Algebra (Fq l bk.a)⟦X⟧ (OCb l) := ek.toAlgebra
  have halg : ∀ a, algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a = ek a := fun _ => rfl
  haveI : Module.IsTorsionFree (Fq l bk.a)⟦X⟧ (OCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  let pr : OCb l →ₗ[(Fq l bk.a)⟦X⟧] (Fq l bk.a)⟦X⟧ :=
    { toFun := prA
      map_add' := prA.map_add
      map_smul' := fun a y => by rw [Algebra.smul_def, halg, hpr, RingHom.id_apply, smul_eq_mul] }
  have hEq : ∀ (T : Type) [CommRing T] (i₁ i₂ : OCb l →+* T),
      (∀ a, i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = i₂ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      IsUnit (i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x' j) - i₂ (x' j) = ∑ i, (i₁ (x' i) - i₂ (x' i)) ^ l * c i j := by
    intro T _ i₁ i₂ hag hu
    have hag' : ∀ a, i₁ (ek a) = i₂ (ek a) := hag
    rw [halg, hX] at hu
    have hf : i₁ bk.flat = i₂ bk.flat := by rw [← hX]; exact hag' X
    obtain ⟨j₁, hj₁⟩ := exists_ext hH i₁ hu
    obtain ⟨j₂, hj₂⟩ := exists_ext hH i₂ (hf ▸ hu)
    have hOE : ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), j₁ y = j₂ y := by
      intro y hy
      obtain ⟨n, s, hs⟩ := (hoe y).1 hy
      have hs' : i₁ ((bk.ev s).coeff 0) = i₂ ((bk.ev s).coeff 0) := by rw [← hek s]; exact hag' _
      have e1 := congrArg j₁ hs
      have e2 := congrArg j₂ hs
      rw [map_mul, map_pow, hj₁, hj₁, hs'] at e1
      rw [map_mul, map_pow, hj₂, hj₂, ← hf] at e2
      exact (hu.pow n).mul_left_cancel (e1.trans e2.symm)
    obtain ⟨c, hc'⟩ := hφ T j₁ j₂ hOE
    obtain ⟨υ, hυ⟩ := hu
    refine ⟨fun i j => c i j * (υ : T) ^ m * ((υ⁻¹ : Tˣ) : T) ^ (m * l), fun j => ?_⟩
    have hx1 : ∀ i, i₁ (x' i) = (υ : T) ^ m * j₁ (x i) := fun i => by
      rw [← hj₁, ← hx' i, map_mul, map_pow, hj₁, ← hυ]
    have hx2 : ∀ i, i₂ (x' i) = (υ : T) ^ m * j₂ (x i) := fun i => by
      rw [← hj₂, ← hx' i, map_mul, map_pow, hj₂, ← hf, ← hυ]
    have hinv : (υ : T) ^ (m * l) * ((υ⁻¹ : Tˣ) : T) ^ (m * l) = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    simp only [hx1, hx2]
    rw [← mul_sub, hc' j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, mul_pow, ← pow_mul]
    linear_combination (-((υ : T) ^ m * (j₁ (x i) - j₂ (x i)) ^ l * c i j)) * hinv
  have hPts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (ψ ψ' : OCb l →+* O), ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X) ≠ 0 →
      ¬ IsUnit (ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      IsAdicComplete (Ideal.span {ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)}) O →
      (∀ a, ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = ψ' (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      ∀ j, ψ (x' j) = ψ' (x' j) := by
    intro O _ _ _ _ _ ψ ψ' h1 h2 h3 hag j
    rw [halg, hX] at h1 h2 h3
    have hag' : ∀ a, ψ (ek a) = ψ' (ek a) := hag
    obtain ⟨g, hg, hψ⟩ := GlobalTheory.T.exists_fixFlat_of_tilt_maps_agree l K bk O ψ h1 h2 h3 ψ' (fun s => by rw [← hek s]; exact hag' _)
    have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
    rw [hψ]
    congr 1
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← galTilt_apply, ← autCb_alg, ← hx' j, map_mul, map_pow, autCb_alg, hfix g hg j, galTilt_apply, hg']
  have hnz : algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X ∈ nonZeroDivisors (OCb l) := by
    rw [halg, hX]; exact mem_nonZeroDivisors_of_ne_zero h0
  have hHX : IsHausdorff (Ideal.span {algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X}) (OCb l) := by
    rw [halg, hX]; exact hH
  have key := GlobalTheory.T.descent_of_points_killed_alt l (Fq l bk.a)⟦X⟧ (OCb l) X pr (CharP.cast_eq_zero _ _) hnz hHX κ x' hEq hPts hpr1
  intro j
  obtain ⟨s, hs⟩ := map_constantCoeff_surj (l := l) (prA (x' j))
  refine (hoe (x j)).2 ⟨m, s, ?_⟩
  rw [hx' j, ← hek s, hs]
  exact congrArg _ (key j)

end GlobalTheory.BSP.TwoCopy
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantMemReductionOfFrobeniusEquationStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) → (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T), (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  first | exact @GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | exact GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | (intros; apply GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant <;> assumption)
end
end
