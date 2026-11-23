module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveMapIntegersClToWittQuotientStatement
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfectStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisEqEmbeddingsOCModPrime

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EmbTwo

theorem range_eq_of_normal {F E L : Type} [Field F] [Field E] [Algebra F E] [Normal F E] [Field L]
    [Algebra F L] (φ ψ : E →ₐ[F] L) : φ.fieldRange = ψ.fieldRange := by
  let e : E ≃ₐ[F] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal F ψ.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
  rw [← h]
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem exists_approx (y : OC l) : ∃ (z : OC l) (w : OC l), (∃ z' : Om l, (z : ℂ_[l]) = (z' : ℂ_[l])) ∧
    y = z + (l : OC l) * w := by
  have hl : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  obtain ⟨z', hz'⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt (y : ℂ_[l]) hl
  set w : ℂ_[l] := (y : ℂ_[l]) - (z' : ℂ_[l]) with hw
  have hw1 : ‖w‖ < ‖((l : ℕ) : ℂ_[l])‖ := by rw [hw, ← dist_eq_norm]; exact hz'
  have hwO : w ∈ 𝓞_ℂ_[l] := (GlobalTheory.RingBasics.mem_OC _).2 (hw1.le.trans GlobalTheory.RingBasics.norm_p_lt.le)
  have hzO : (z' : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    have : (z' : ℂ_[l]) = (y : ℂ_[l]) - w := by rw [hw]; ring
    rw [this]; exact Subring.sub_mem _ y.2 hwO
  have hq : w / ((l : ℕ) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC, norm_div, div_le_one hl]; exact hw1.le
  refine ⟨⟨_, hzO⟩, ⟨_, hq⟩, ⟨z', rfl⟩, Subtype.ext ?_⟩
  push_cast
  rw [mul_div_cancel₀ _ GlobalTheory.RingBasics.p_ne_zero, hw]; ring

end GlobalTheory.EmbTwo


open GlobalTheory.EmbTwo in
theorem GlobalTheory.EmbTwo.exists_gal_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (D : Type) [CommRing D] [IsDomain D] (θ₁ θ₂ : OC l →+* D), Function.Injective θ₁ → Function.Injective θ₂ → (∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r)) → ∃ g : ↥(GK K), (∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO (g : GQ l) y)) ∧ ∀ y : OC l, ((l : ℕ) : D) ∣ θ₂ y - θ₁ (Per.σO (g : GQ l) y) := by
  intro l _ K D _ _ θ₁ θ₂ h1 h2 hK
  let F := FractionRing D
  have i1 : Function.Injective ((algebraMap D F).comp θ₁) := (IsFractionRing.injective D F).comp h1
  have i2 : Function.Injective ((algebraMap D F).comp θ₂) := (IsFractionRing.injective D F).comp h2
  let τ₁ : ℂ_[l] →+* F := IsFractionRing.lift i1
  let τ₂ : ℂ_[l] →+* F := IsFractionRing.lift i2
  let σ₁ : Om l →+* F := τ₁.comp (algebraMap (Om l) ℂ_[l])
  let σ₂ : Om l →+* F := τ₂.comp (algebraMap (Om l) ℂ_[l])
  have hτ₁ : ∀ y : OC l, τ₁ (y : ℂ_[l]) = algebraMap D F (θ₁ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i1 y
  have hτ₂ : ∀ y : OC l, τ₂ (y : ℂ_[l]) = algebraMap D F (θ₂ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i2 y

  have hO : ∀ r : ↥(OL K), σ₁ ((r : ↥K.1) : Om l) = σ₂ ((r : ↥K.1) : Om l) := fun r => by
    change τ₁ ((intToOC K r : OC l) : ℂ_[l]) = τ₂ ((intToOC K r : OC l) : ℂ_[l])
    rw [hτ₁, hτ₂, hK]

  have hKK : ∀ x : ↥K.1, σ₁ (x : Om l) = σ₂ (x : Om l) := fun x => by
    have ha : IsAlgebraic ℤ_[l] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
    let r : ↥(OL K) := ⟨y • x, hy⟩
    let s : ↥(OL K) := algebraMap ℤ_[l] ↥(OL K) y
    have hrs : ((r : ↥K.1) : Om l) = ((s : ↥K.1) : Om l) * (x : Om l) := by
      change ((y • x : ↥K.1) : Om l) = _
      rw [Algebra.smul_def]; rfl
    have hs0 : ((s : ↥K.1) : Om l) ≠ 0 := by
      intro h0
      apply hy0
      have : (s : ↥K.1) = 0 := Subtype.ext h0
      have h3 : algebraMap ℤ_[l] ↥K.1 y = 0 := this
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1, _root_.map_eq_zero] at h3
      exact (IsFractionRing.injective ℤ_[l] ℚ_[l]) (h3.trans (map_zero _).symm)
    have e1 := hO r
    rw [hrs, map_mul, map_mul, hO s] at e1
    exact mul_left_cancel₀ ((map_ne_zero σ₂).2 hs0) e1
  letI : Algebra ↥K.1 F := (σ₁.comp (algebraMap ↥K.1 (Om l))).toAlgebra
  let φ₁ : Om l →ₐ[↥K.1] F := { σ₁ with commutes' := fun _ => rfl }
  let φ₂ : Om l →ₐ[↥K.1] F := { σ₂ with commutes' := fun x => (hKK x).symm }
  have hR := range_eq_of_normal φ₁ φ₂
  let e₁ : Om l ≃ₐ[↥K.1] φ₁.fieldRange := AlgEquiv.ofInjectiveField φ₁
  have hmem : ∀ z, φ₂ z ∈ φ₁.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : Om l →ₐ[↥K.1] Om l := e₁.symm.toAlgHom.comp (φ₂.codRestrict φ₁.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, σ₁ (g₀ z) = σ₂ z := fun z => by
    have := congrArg Subtype.val (e₁.apply_symm_apply ⟨φ₂ z, hmem z⟩)
    exact this
  let g₁ : Om l ≃ₐ[↥K.1] Om l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  let g : GQ l := g₁.restrictScalars ℚ_[l]
  have hgK : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g₀.commutes ⟨x, hx⟩
  have hg : ∀ z : Om l, σ₁ (g z) = σ₂ z := hg₀
  have c1 : ∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO g y) := by
    rintro y ⟨z, hz⟩
    apply IsFractionRing.injective D F
    rw [← hτ₁, ← hτ₂]
    have e2 : ((Per.σO g y : OC l) : ℂ_[l]) = ((g z : Om l) : ℂ_[l]) := by
      refine (GlobalTheory.RingIface.sigO_coe l g y).trans ?_
      rw [hz, GlobalTheory.RingBasics.σC_coe]
    rw [e2, hz]
    exact (hg z).symm
  refine ⟨⟨g, hgK⟩, c1, fun y => ?_⟩
  obtain ⟨z, w, hz, rfl⟩ := exists_approx y
  refine ⟨θ₂ w - θ₁ (Per.σO g w), ?_⟩
  have := c1 z hz
  simp only [map_add (f := _), map_mul, map_natCast]
  rw [this]; ring
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisEqEmbeddingsOCModPrimeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_galois_eq_embeddings_OC_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (D : Type) [CommRing D] [IsDomain D] (θ₁ θ₂ : OC l →+* D), Function.Injective θ₁ → Function.Injective θ₂ → (∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r)) → ∃ g : ↥(GK K), (∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO (g : GQ l) y)) ∧ ∀ y : OC l, ((l : ℕ) : D) ∣ θ₂ y - θ₁ (Per.σO (g : GQ l) y) := by
  first | exact @GlobalTheory.EmbTwo.exists_gal_eq | exact GlobalTheory.EmbTwo.exists_gal_eq | (intros; apply GlobalTheory.EmbTwo.exists_gal_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfPerfectOfDvdSubAdicSeparated

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory

theorem ringHom_eq_of_perfect_of_dvd_sub :
    ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  intro l _ R O _ _ _ _ _ x e he hH ψ ψ' h
  ext y
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  obtain ⟨z, rfl⟩ : ∃ z : R, z ^ l ^ n = y :=
    ⟨(iterateFrobeniusEquiv R l n).symm y, by
      have hs := (iterateFrobeniusEquiv R l n).apply_symm_apply y
      rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hs⟩
  rw [map_pow, map_pow, ← sub_pow_char_pow]
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hn : n ≤ e * l ^ n :=
    (Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_left _ he)
  exact (pow_dvd_pow x hn).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd (h z) _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfPerfectOfDvdSubAdicSeparatedStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  first | exact @GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | exact GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | (intros; apply GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorMapBreuilKisinEvEq

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wmap_ev_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ bk.flat ≠ 0 →
    IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∀ s : bk.S, WittVector.map ψ (bk.ev s) = WittVector.map ψ' (bk.ev s) := by
  intro l _ K bk O _ _ _ _ ψ ψ' h0 hc h s
  have hval : ∀ y : Fq l bk.a, ψ (Fq.val l bk.a y) = ψ' (Fq.val l bk.a y) := fun y => by
    have := h (C (WittVector.teichmuller l y))
    rwa [bk.ev_C, wA_teich, WittVector.teichmuller_coeff_zero] at this
  have hflat : ψ bk.flat = ψ' bk.flat := by
    have := h X
    rwa [bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  have hX : ((WittVector.map ψ).comp bk.ev) X = WittVector.teichmuller l (ψ bk.flat) := by
    rw [RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller]
  have hcomp := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) h0 hc).1
  refine RingHom.congr_fun (ringHom_ext_of_sep ((WittVector.map ψ).comp bk.ev) ((WittVector.map ψ').comp bk.ev)
    (fun w => ?_) ?_ fun x hx => ?_) s
  · simp only [RingHom.comp_apply, bk.ev_C]
    refine WittVector.ext fun n => ?_
    simp only [wA, AlgHom.coe_mk, WittVector.map_coeff]
    exact hval _
  · rw [hX, RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller, hflat]
  · rw [hX] at hx
    refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l (ψ bk.flat)}) x fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 (hx n)

end GlobalTheory.BSP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorMapBreuilKisinEvEqStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.wittVector_map_breuilKisin_ev_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ bk.flat ≠ 0 → IsAdicComplete (Ideal.span {ψ bk.flat}) O → (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) → ∀ s : bk.S, WittVector.map ψ (bk.ev s) = WittVector.map ψ' (bk.ev s) := by
  first | exact @GlobalTheory.BSP.wmap_ev_eq | exact GlobalTheory.BSP.wmap_ev_eq | (intros; apply GlobalTheory.BSP.wmap_ev_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixFlatOfTiltMapsAgree

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_galK_fixFlat_of_tilt_maps_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type)
    [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O),
    ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    ∀ ψ' : OCb l →+* O, (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∃ g : ↥(GK K), bk.FixFlat g ∧ ∀ y, ψ' y = ψ (Per.σF (g : GQ l) y) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc ψ' hs
  have hflat : ψ' bk.flat = ψ bk.flat := by
    have h := hs X
    rw [bk.ev_X, WittVector.teichmuller_coeff_zero] at h
    exact h.symm
  have hW := GlobalTheory.T.wittVector_map_breuilKisin_ev_eq l K bk O ψ ψ' h0 hc hs
  obtain ⟨θ₁, hθ₁, hinj₁, hdom, hdiv⟩ := GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc
  obtain ⟨θ₂', hθ₂', hinj₂', -, -⟩ :=
    GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ' (hflat ▸ h0) (hflat ▸ hu) (hflat ▸ hc)
  have hI : Ideal.span {WittVector.map ψ' (bk.ev bk.E)} = Ideal.span {WittVector.map ψ (bk.ev bk.E)} := by
    rw [hW bk.E]
  let θ₂ := (Ideal.quotEquivOfEq hI).toRingHom.comp θ₂'
  have hθ₂ : ∀ a : Ainf l, θ₂ (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ' a) := by
    intro a
    simp only [θ₂, RingHom.comp_apply, hθ₂' a, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      Ideal.quotEquivOfEq_mk]
  have hinj₂ : Function.Injective θ₂ := (Ideal.quotEquivOfEq hI).injective.comp hinj₂'
  haveI := hdom
  have hK : ∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r) := by
    intro r
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (bk.str r)
    rw [← bk.θ_ev r x hx, hθ₁, hθ₂, hW x]
  obtain ⟨g, halg, hl⟩ := GlobalTheory.T.exists_galois_eq_embeddings_OC_mod_prime l K _ θ₁ θ₂ hinj₁ hinj₂ hK
  obtain ⟨hroot, hfix⟩ := GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk

  have key : ∀ z : OCb l, ψ z = ψ' z →
      ψ ((frobeniusEquiv (OCb l) l).symm z) = ψ' ((frobeniusEquiv (OCb l) l).symm z) := by
    intro z hz
    apply frobenius_inj O l
    rw [← RingHom.map_frobenius, ← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, hz]
  have hiter : ∀ n : ℕ, ψ (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) =
      ψ' (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) := by
    intro n
    induction n with
    | zero => exact hflat.symm
    | succ n ih => rw [Function.iterate_succ_apply']; exact key _ ih
  have hθroot : ∀ n : ℕ, θ₁ (GlobalTheory.MemLoc.rootT bk.flat n) = θ₂ (GlobalTheory.MemLoc.rootT bk.flat n) := by
    intro n
    have e : GlobalTheory.MemLoc.rootT bk.flat n =
        Per.θ l (WittVector.teichmuller l (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat)) := by
      rw [GlobalTheory.MemLoc.rootT, WittVector.fontaineTheta_teichmuller]
    rw [e, hθ₁, hθ₂, WittVector.map_teichmuller, WittVector.map_teichmuller, hiter n]
  refine ⟨g, ?_, ?_⟩
  · refine hfix (g : GQ l) bk.flat fun n => ?_
    obtain ⟨z, hz⟩ := hroot n
    have h := halg _ ⟨z, hz⟩
    rw [← hθroot n] at h
    exact (hinj₁ h).symm
  · have hext := GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated l (OCb l) O (ψ bk.flat) bk.Ep.natDegree bk.deg_pos hc.toIsHausdorff
      ψ' (ψ.comp (Per.σF (g : GQ l))) fun y => ?_
    · intro y
      exact RingHom.congr_fun hext y
    · have hmk := hl (Per.θ l (WittVector.teichmuller l y))
      rw [← GlobalTheory.RingBasics.θ_σA, hθ₁, hθ₂] at hmk
      have e2 : Per.σA (g : GQ l) (WittVector.teichmuller l y) =
          WittVector.teichmuller l (Per.σF (g : GQ l) y) := by
        exact GlobalTheory.RingIface.sigA_teich l (g : GQ l) y
      rw [e2, WittVector.map_teichmuller, WittVector.map_teichmuller, ← map_sub] at hmk
      have h := hdiv _ hmk
      rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
        WittVector.teichmuller_coeff_zero] at h
      simpa [RingHom.comp_apply] using h

end GlobalTheory.BSP
end
end
