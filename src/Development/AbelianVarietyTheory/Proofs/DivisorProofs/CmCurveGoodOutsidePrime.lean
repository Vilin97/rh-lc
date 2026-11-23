module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledPeriodPairInvariantsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtNegPrimeKernelDatumOfIntegersLatticeStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersLatticeInvariantsNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplierStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMinimalOfDiscrEqUnitMulNegCubeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNegStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTwistCmCurveModelDiscriminantNegPrimeCuStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralOfModelAt

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_integral_of_modelAt (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F)
    (hV : ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) (hD : D ≠ 0)
    (h : ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ)) :
    ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ),
      (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧
        (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  have hu0 : (⟨(C.u : ℂ), hu⟩ : F) ≠ 0 := by
    intro h0
    exact C.u.ne_zero (congrArg (fun x : F => (x : ℂ)) h0)
  let C' : VariableChange F := ⟨Units.mk0 _ hu0, ⟨C.r, hr⟩, ⟨C.s, hs⟩, ⟨C.t, ht⟩⟩
  have hC : C'.map (algebraMap F ℂ) = C := by
    ext <;> rfl
  have hmap : (C' • A).map (algebraMap F ℂ) = C • A.map (algebraMap F ℂ) := by
    rw [← hC, map_variableChange]
  rw [← hmap] at h1 h2 h3 h4 h6 hΔ
  set W := C' • A with hW
  have hD' : (D : ℂ) ≠ 0 := fun h0 => hD (Subtype.ext h0)
  have hvD : V.valuation (D : ℂ) ≠ 0 := by simpa using hD'
  rw [map_Δ] at hΔ
  have hΔ' : V.valuation ((W.Δ : F) : ℂ) = V.valuation (D : ℂ) := hΔ
  have hW0 : W.Δ ≠ 0 := by
    intro h0
    rw [h0] at hΔ'
    exact hvD (by simpa using hΔ'.symm)
  have hx : W.Δ / D ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  have hy : D / W.Δ ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  refine ⟨C', ⟨⟨_, hx⟩, ⟨_, hy⟩, ?_, ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    show W.Δ / D * (D / W.Δ) = 1
    field_simp
  · apply Subtype.ext
    show D / W.Δ * (W.Δ / D) = 1
    field_simp
  · refine ⟨⟨⟨⟨W.a₁, (hV _).1 h1⟩, ⟨W.a₂, (hV _).1 h2⟩, ⟨W.a₃, (hV _).1 h3⟩, ⟨W.a₄, (hV _).1 h4⟩,
      ⟨W.a₆, (hV _).1 h6⟩⟩, ?_⟩⟩
    ext <;> rfl
  · show W.Δ = W.Δ / D * D
    field_simp

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralOfModelAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F), (∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) → D ≠ 0 → ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ) → ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ), (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧ (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  first | exact @GlobalTheory.CMModel.exists_integral_of_modelAt | exact GlobalTheory.CMModel.exists_integral_of_modelAt | (intros; apply GlobalTheory.CMModel.exists_integral_of_modelAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLatticeProdDerivWeierstrassPMem

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_datum_sqProd_mem :
    ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p →
      Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧
        (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  intro p F L t hp h4 h3 hD
  set c := sqProd p L t with hc
  have hc0 : c ≠ 0 := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
  have hc2 : c ^ 2 ∈ F := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp h4 h3 hD).1
  obtain ⟨L', hlat, hg₂, hg₃, hder, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L c hc0
  obtain ⟨hcard, -⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4
  refine ⟨L', c * t, ⟨?_, ?_, ?_, ?_, ?_⟩, hj, ?_⟩
  · intro ω hω
    have hz : c * (c⁻¹ * ω) ∈ L'.lattice := by rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hz' := (hlat _).1 hz
    have := (hlat _).2 (hD.mul _ hz')
    rwa [← mul_assoc, mul_comm c, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc0, one_mul] at this
  · rw [hg₂]
    have : (c ^ 4)⁻¹ = ((c ^ 2) ^ 2)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₂_mem
  · rw [hg₃]
    have : (c ^ 6)⁻¹ = ((c ^ 2) ^ 3)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₃_mem
  · rw [hlat]; exact hD.notMem
  · have := (hlat _).2 hD.ker
    rwa [← mul_assoc, mul_comm c, mul_assoc] at this
  · have hprod : sqProd p L' (c * t) = ((c ^ 3)⁻¹) ^ Fintype.card (Sq p) * c := by
      unfold sqProd
      have : ∀ k : Sq p, L'.derivWeierstrassP (sqPt p (c * t) k) =
          (c ^ 3)⁻¹ * L.derivWeierstrassP (sqPt p t k) := by
        intro k
        unfold sqPt
        rw [← hder, ← mul_assoc, mul_comm ((k.1 : ℕ) : ℂ) c, mul_assoc]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, hc]
      rfl
    rw [hprod]
    set n := Fintype.card (Sq p) with hn
    have : ((c ^ 3)⁻¹) ^ n * c = ((c ^ 2) ^ (3 * ((n - 1) / 2) + 1))⁻¹ := by
      obtain ⟨m, hm⟩ : Odd n := (GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4).2
      rw [hm]
      have : (2 * m + 1 - 1) / 2 = m := by omega
      rw [this]
      apply eq_inv_of_mul_eq_one_left
      rw [inv_pow, mul_assoc, show c * (c ^ 2) ^ (3 * m + 1) = (c ^ 3) ^ (2 * m + 1) by ring,
        inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc0))]
    rw [this]
    exact inv_mem (pow_mem hc2 _)

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLatticeProdDerivWeierstrassPMemStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧ (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  first | exact @GlobalTheory.CMModel.exists_datum_sqProd_mem | exact GlobalTheory.CMModel.exists_datum_sqProd_mem | (intros; apply GlobalTheory.CMModel.exists_datum_sqProd_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringComplexOverPrime

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_valuationSubring_complex_over_prime :
    ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
      ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  intro F _ w
  set R := w.valuationSubringAtPrime F with hR
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    ((algebraMap F ℂ).comp R.subtype)
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hV ⟨x, hx⟩⟩⟩
  by_contra hxR
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxR R.zero_mem
  have hinv : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hxR
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hu : IsUnit ((((algebraMap F ℂ).comp R.subtype).codRestrict V.toSubring hV) ⟨x⁻¹, hinv⟩) := by
    refine IsUnit.of_mul_eq_one ⟨(x : ℂ), hx⟩ ?_
    apply Subtype.ext
    change ((x⁻¹ : F) : ℂ) * (x : ℂ) = 1
    rw [IntermediateField.coe_inv, inv_mul_cancel₀ hx0']
  have hu' : IsUnit (⟨x⁻¹, hinv⟩ : R) := hloc.map_nonunit _ hu
  obtain ⟨y, hy⟩ := hu'.exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : x = (y : F) := by
    have h := congrArg (x * ·) hy'
    simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at h
    exact h.symm
  exact hxR (this ▸ y.2)

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringComplexOverPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)), ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  first | exact @GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | exact GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | (intros; apply GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmCurveGoodOutsidePrime

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem shortTwist_Δ (d a b : ℂ) :
    (shortTwist d a b).Δ = d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortTwist_c₄ (d a b : ℂ) :
    (shortTwist d a b).c₄ = d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [shortTwist, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem shortTwist_j {d a b : ℂ} (hd : d ≠ 0) [(shortTwist d a b).IsElliptic]
    [(⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).IsElliptic] :
    (shortTwist d a b).j = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).j := by
  have h0 : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ ≠ 0 :=
    (WeierstrassCurve.IsElliptic.isUnit (W := (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ))).ne_zero
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    shortTwist_Δ, shortTwist_c₄]
  field_simp

theorem j_congr_of_eq {W W' : WeierstrassCurve ℂ} (h : W = W') [W.IsElliptic] [W'.IsElliptic] :
    W.j = W'.j := by
  subst h; rfl

end GlobalTheory.CMModel

namespace GlobalTheory.Published

theorem cmCurveGoodOutsidePrime : CMCurveGoodOutsidePrimeSt := by
  intro p hp h4 h3
  obtain ⟨L₀, hL₀⟩ := exists_isIntegersLattice (p := p) hp.pos
  obtain ⟨-, -, hms⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  have him : (sqrtNegNat p).im ≠ 0 := by
    simp only [sqrtNegNat, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  have hjint := GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L₀ (sqrtNegNat p) hms him
  have hjQ : IsIntegral ℚ (latticeCurve L₀).j := hjint.tower_top
  haveI : FiniteDimensional ℚ ℚ⟮(latticeCurve L₀).j⟯ := IntermediateField.adjoin.finiteDimensional hjQ
  haveI hNF : NumberField ℚ⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite ℚ _
  obtain ⟨L₁, t₁, hD₁, hj₁⟩ := GlobalTheory.T.exists_sqrtNegPrimeKernelDatum_of_integersLattice p L₀ hp h4 h3 hL₀
  obtain ⟨L, t, hD, hj, hsq⟩ := GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem p _ L₁ t₁ hp h4 h3 hD₁
  set F := ℚ⟮(latticeCurve L₀).j⟯ with hFdef
  have hg₂ : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) (ofNat_mem _ 4)
  have hg₃ : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) (ofNat_mem _ 4)
  let dF : F := if p % 8 = 3 then 1 else -(p : F)
  let dC : ℂ := if p % 8 = 3 then 1 else -(p : ℂ)
  have hdC : ((dF : F) : ℂ) = dC := by
    simp only [dF, dC]; split_ifs <;> simp
  have hdC0 : dC ≠ 0 := by
    simp only [dC]; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr (by exact_mod_cast hp.ne_zero)
  let A : WeierstrassCurve F := shortTwist dF ⟨-L.g₂ / 4, hg₂⟩ ⟨-L.g₃ / 4, hg₃⟩
  have hmap : A.map (algebraMap F ℂ) = shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4) := by
    rw [← hdC]
    ext <;> simp [A, shortTwist, WeierstrassCurve.map]
  have hlat : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L := rfl
  have hΔA : A.Δ ≠ 0 := by
    intro h0
    have := congrArg (algebraMap F ℂ) h0
    rw [← WeierstrassCurve.map_Δ, hmap, shortTwist_Δ, hlat, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hdC0) (latticeCurve_Δ_ne_zero L) this
  haveI hE : A.IsElliptic := ⟨Ne.isUnit hΔA⟩
  have hmin : HasMinimalDiscriminant A (-(p : F) ^ 3) := by
    intro w
    obtain ⟨V, hV⟩ := GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime F w
    have hloc := GlobalTheory.T.quadraticTwist_cmCurve_model_discriminant_negPrimeCube p F L t hp h4 h3 hD hsq V
    have hD0 : (-(p : F) ^ 3) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    have hmod : ModelAt V F (A.map (algebraMap F ℂ)) ((-(p : F) ^ 3 : F) : ℂ) := by
      rw [hmap]
      convert hloc using 1
    obtain ⟨C, u, hI, hΔ⟩ := GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt F w V A _ hV hD0 hmod
    have hram := GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg p L₀ w hp hL₀
    exact ⟨C, u, GlobalTheory.T.isMinimal_of_discr_eq_unit_mul_neg_prime_cube p F w (C • A) u hram hI hΔ, hΔ⟩
  refine ⟨F, hNF, A, ⟨hNF, hE, L₀, hL₀, rfl, ?_, hmin.hasGoodReductionOutside⟩, hmin⟩
  have e1 : ((A.j : F) : ℂ) = (A.map (algebraMap F ℂ)).j := (A.map_j (algebraMap F ℂ)).symm
  haveI : (shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4)).IsElliptic := hmap ▸ inferInstance
  haveI : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ).IsElliptic :=
    inferInstanceAs (latticeCurve L).IsElliptic
  rw [e1, j_congr_of_eq hmap, shortTwist_j hdC0, j_congr_of_eq hlat, hj, hj₁]

end GlobalTheory.Published
end
end
