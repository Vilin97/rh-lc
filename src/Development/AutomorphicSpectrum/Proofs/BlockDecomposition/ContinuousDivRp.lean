module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
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
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.ProperAction.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BochnerTheorem.RMKComplex

section

@[expose] public section

noncomputable section

open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported

namespace PI.Bochner

variable {X : Type*} [TopologicalSpace X]

def ofR (g : C(X, ℝ)) : C(X, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩

@[simp] lemma ofR_apply (g : C(X, ℝ)) (x : X) : ofR g x = (g x : ℂ) := rfl

lemma ofR_add (g h : C(X, ℝ)) : ofR (g + h) = ofR g + ofR h := by
  ext x
  simp

lemma ofR_sub (g h : C(X, ℝ)) : ofR (g - h) = ofR g - ofR h := by
  ext x
  simp

lemma ofR_smul (c : ℝ) (g : C(X, ℝ)) : ofR (c • g) = (c : ℂ) • ofR g := by
  ext x
  simp

def reC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩

def imC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩

lemma eq_ofR_re_add_im (f : C(X, ℂ)) : f = ofR (reC f) + Complex.I • ofR (imC f) := by
  ext x
  apply Complex.ext <;> simp [reC, imC]

section
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ

lemma nonneg_ofR {g : C(X, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ Λ (ofR g) := by
  have e : ofR g = star (ofR ⟨fun x => Real.sqrt (g x), by fun_prop⟩) *
      ofR ⟨fun x => Real.sqrt (g x), by fun_prop⟩ := by
    ext x
    simp only [ofR_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.coe_mk,
      Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg x)]
  rw [e]
  exact hΛ _

lemma im_ofR (g : C(X, ℝ)) : (Λ (ofR g)).im = 0 := by
  have hp : ∀ h : C(X, ℝ), (∀ x, 0 ≤ h x) → (Λ (ofR h)).im = 0 := fun h hh =>
    ((Complex.nonneg_iff.1 (nonneg_ofR Λ hΛ hh)).2).symm
  rw [← posPart_sub_negPart g, ofR_sub, map_sub, Complex.sub_im,
    hp _ (fun x => ContinuousMap.le_def.1 (posPart_nonneg g) x),
    hp _ (fun x => ContinuousMap.le_def.1 (negPart_nonneg g) x), sub_zero]

lemma ofR_eq_re (g : C(X, ℝ)) : Λ (ofR g) = ((Λ (ofR g)).re : ℂ) := by
  exact Complex.ext (by simp) (by simp [im_ofR Λ hΛ g])

end

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem exists_measure_of_positive (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ := by
  let e := CompactlySupportedContinuousMap.continuousMapEquiv (α := X) (β := ℝ)
  let L : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun f => (Λ (ofR (e.symm f))).re
      map_add' := fun f g => by
        have h1 : e.symm (f + g) = e.symm f + e.symm g := by ext x; simp [e]
        simp only [h1, ofR_add, map_add (f := _), Complex.add_re]
      map_smul' := fun c f => by
        have h1 : e.symm (c • f) = c • e.symm f := by ext x; simp [e]
        simp only [h1, ofR_smul, map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply] }
  let Lp := PositiveLinearMap.mk₀ L (fun f hf => by
    show 0 ≤ (Λ (ofR (e.symm f))).re
    have hfx : ∀ x, 0 ≤ (e.symm f) x := fun x => by
      have h2 : (0 : CompactlySupportedContinuousMap X ℝ) x ≤ f x := hf x
      simpa [e] using h2
    exact (Complex.nonneg_iff.1 (nonneg_ofR Λ hΛ hfx)).1)
  refine ⟨RealRMK.rieszMeasure Lp, inferInstance, fun f => ?_⟩
  have hint : ∀ g : C(X, ℝ), ∫ x, g x ∂(RealRMK.rieszMeasure Lp) = (Λ (ofR g)).re := fun g => by
    have h := RealRMK.integral_rieszMeasure Lp (e g)
    have h3 : e.symm (e g) = g := e.symm_apply_apply g
    simp only [e, CompactlySupportedContinuousMap.continuousMapEquiv_apply_toFun] at h
    rw [h]
    show (Λ (ofR (e.symm (e g)))).re = _
    rw [h3]
  have hI : Integrable (fun x => f x) (RealRMK.rieszMeasure Lp) := by
    first
      | exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      | exact ContinuousMap.integrable f
      | exact (integrableOn_univ).1 (f.continuous.continuousOn.integrableOn_compact isCompact_univ)
  conv_lhs => rw [eq_ofR_re_add_im f]
  rw [map_add (f := _), map_smul, ofR_eq_re Λ hΛ, ofR_eq_re Λ hΛ (imC f), ← hint, ← hint, smul_eq_mul,
    ← integral_re_add_im hI]
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex]
  rw [mul_comm]
  rfl

end PI.Bochner
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDivRp

section

@[expose] public section

noncomputable section

open MeasureTheory Topology
open scoped ComplexOrder ComplexConjugate

namespace GlobalTheory.CompanionTheory.RswCell

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

def secOf (P : Subgroup G) (h : G → ℝ) (F : G ⧸ P → ℂ) (g : G) : ℂ :=
  F (QuotientGroup.mk g⁻¹) * (h g : ℂ)

theorem mk_inv_mul {P : Subgroup G} {p : G} (hp : p ∈ P) (g : G) :
    (QuotientGroup.mk (p * g)⁻¹ : G ⧸ P) = QuotientGroup.mk g⁻¹ := by
  rw [mul_inv_rev]
  exact QuotientGroup.mk_mul_of_mem _ (P.inv_mem hp)

theorem div_rp {P : Subgroup G} {h : G → ℝ} {f : G → ℂ} (hpos : ∀ g, 0 < h g) (hf : Sec P h f) (g : G) :
    f (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) / (h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) : ℂ) =
      f g / (h g : ℂ) := by
  obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P g⁻¹
  have hr : rp (QuotientGroup.mk g⁻¹ : G ⧸ P) = (p : G)⁻¹ * g := by
    show (Quotient.out (QuotientGroup.mk g⁻¹ : G ⧸ P))⁻¹ = _
    rw [hp, mul_inv_rev, inv_inv]
  rw [hr]
  have key := hf.2 (p : G)⁻¹ (P.inv_mem p.2) g
  have h1 : (h ((p : G)⁻¹ * g) : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  have h2 : (h g : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  rw [div_eq_div_iff h1 h2]
  exact key

variable [IsTopologicalGroup G]

theorem secOf_sec {P : Subgroup G} {h : G → ℝ} (hc : Continuous h) {F : G ⧸ P → ℂ}
    (hF : Continuous F) : Sec P h (secOf P h F) := by
  refine ⟨?_, fun p hp g => ?_⟩
  · unfold secOf
    exact (hF.comp (QuotientGroup.continuous_mk.comp continuous_inv)).mul
      (Complex.continuous_ofReal.comp hc)
  · unfold secOf
    rw [mk_inv_mul hp g]
    ring

theorem compact_quot {P : Subgroup G}
    (hco : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c) : CompactSpace (G ⧸ P) := by
  obtain ⟨C, hC, hcov⟩ := hco
  have huniv : (Set.univ : Set (G ⧸ P)) = (fun c => (QuotientGroup.mk c⁻¹ : G ⧸ P)) '' C := by
    ext x
    simp only [Set.mem_univ, Set.mem_image, true_iff]
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq, c, hc, hac⟩ := hcov a⁻¹
    refine ⟨c, hc, ?_⟩
    have ha : a = c⁻¹ * q⁻¹ := by rw [← mul_inv_rev, ← hac, inv_inv]
    rw [ha, QuotientGroup.mk_mul_of_mem _ (P.inv_mem hq)]
  refine ⟨?_⟩
  rw [huniv]
  exact hC.image (QuotientGroup.continuous_mk.comp continuous_inv)

theorem continuous_div_rp {P : Subgroup G} {h : G → ℝ} {f : G → ℂ} (hc : Continuous h)
    (hpos : ∀ g, 0 < h g) (hf : Sec P h f) :
    Continuous fun q : G ⧸ P => f (rp q) / (h (rp q) : ℂ) := by
  rw [(QuotientGroup.isQuotientMap_mk P).continuous_iff]
  have hcomp : ((fun q : G ⧸ P => f (rp q) / (h (rp q) : ℂ)) ∘ QuotientGroup.mk) =
      fun a => f a⁻¹ / (h a⁻¹ : ℂ) := by
    funext a
    have := div_rp hpos hf a⁻¹
    rw [inv_inv] at this
    exact this
  rw [hcomp]
  exact (hf.1.comp continuous_inv).div (Complex.continuous_ofReal.comp (hc.comp continuous_inv))
    fun a => by exact_mod_cast (hpos _).ne'

theorem exists_repr [T2Space G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    (h : G → ℝ) (mu : (G → ℂ) → ℂ) (S : Setup P h mu) : ∃ ν, Repr P h mu ν := by
  haveI : CompactSpace (G ⧸ P) := compact_quot S.cocpt
  haveI : IsClosed (P : Set G) := S.closed
  let Λ : C(G ⧸ P, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun F => mu (secOf P h F)
      map_add' := fun F F' => by
        have he : secOf P h ⇑(F + F') = secOf P h F + secOf P h F' := by
          funext g
          simp only [secOf, ContinuousMap.add_apply, Pi.add_apply]
          ring
        rw [he]
        exact S.add _ _ (secOf_sec S.cont F.continuous) (secOf_sec S.cont F'.continuous)
      map_smul' := fun c F => by
        have he : secOf P h ⇑(c • F) = c • secOf P h F := by
          funext g
          simp only [secOf, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [he]
        exact S.smul c _ (secOf_sec S.cont F.continuous) }
  have hpos : ∀ F : C(G ⧸ P, ℂ), 0 ≤ Λ (star F * F) := by
    intro F
    have hval : ∀ g, secOf P h ⇑(star F * F) g =
        ((Complex.normSq (F (QuotientGroup.mk g⁻¹)) * h g : ℝ) : ℂ) := by
      intro g
      simp only [secOf, ContinuousMap.mul_apply, ContinuousMap.star_apply]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hnn := S.nonneg (secOf P h ⇑(star F * F)) (secOf_sec S.cont (star F * F).continuous)
      (fun g => by
        rw [hval g, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨mul_nonneg (Complex.normSq_nonneg _) (S.pos g).le, rfl⟩)
    exact Complex.nonneg_iff.2 ⟨hnn.1, hnn.2.symm⟩
  obtain ⟨ν, hfin, hrep⟩ := PI.Bochner.exists_measure_of_positive Λ hpos
  refine ⟨ν, hfin, fun f hf => ?_⟩
  let Fc : C(G ⧸ P, ℂ) := ⟨fun q => f (rp q) / (h (rp q) : ℂ), continuous_div_rp S.cont S.pos hf⟩
  have hsec : secOf P h ⇑Fc = f := by
    funext g
    show f (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) / (h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) : ℂ) * (h g : ℂ) = f g
    rw [div_rp S.pos hf g]
    have h2 : (h g : ℂ) ≠ 0 := by exact_mod_cast (S.pos g).ne'
    field_simp
  refine ⟨?_, ?_⟩
  · exact Fc.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · calc mu f = Λ Fc := by
          show mu f = mu (secOf P h ⇑Fc)
          rw [hsec]
      _ = ∫ q, Fc q ∂ν := hrep Fc

theorem riesz : Riesz := by
  intro G _ _ _ _ _ _ P _ _ h mu S
  exact exists_repr P h mu S

end GlobalTheory.CompanionTheory.RswCell
end
end
end
