module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LocalArcIntegralityOfCmNormalisedTrivialisationStatement
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.LinOfPoly
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.FunDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.ExistsCoeffNormOne
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCorePf

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.AlgebraMapArcSInjective

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

namespace FinPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem arcDet_ne_zero (Dw : Datum H) (K₁ : Type) [Field K₁] : arcDet Dw K₁ ≠ 0 := by
  apply Formalism.L2.Pj.QAt.LinOfPoly.arcDet_ne_zero <;> assumption

theorem algebraMap_arcS_injective (Dw : Datum H) (K₁ : Type) [Field K₁] :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)) :=
  IsLocalization.injective (M := Submonoid.powers (arcDet Dw K₁)) (S := ArcS Dw K₁)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K₁))

theorem arcNum_algebraMap {K₁ : Type} [Field K₁] (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :
    arcNum (algebraMap _ (ArcS Dw K₁) P) = P := by
  unfold arcNum
  split
  · rename_i h
    first
      | exact algebraMap_arcS_injective Dw K₁ h.choose_spec
      | exact (algebraMap_arcS_injective Dw K₁ h.choose_spec).symm
      | exact algebraMap_arcS_injective Dw K₁ h.choose_spec.symm
  · rename_i h
    exact absurd ⟨P, rfl⟩ h

theorem zpow_bound {α : Type} (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (o vth : ℤ) (N d m : ℕ) (s : Finset α)
    (e : α → ℕ) (v : α → ℤ)
    (h : r ^ o ≤ (r ^ vth) ^ N * (∏ x ∈ s, (r ^ v x) ^ e x) * (r ^ (-(m : ℤ))) ^ d) :
    (N : ℝ) * vth + ∑ x ∈ s, (e x : ℝ) * v x - m * d ≤ o := by
  have hL : Real.log r < 0 := Real.log_neg hr0 hr1
  have hA : ∀ z : ℤ, 0 < r ^ z := fun z => zpow_pos hr0 z
  have hP : 0 < ∏ x ∈ s, (r ^ v x) ^ e x := Finset.prod_pos fun x _ => pow_pos (hA _) _
  have hlog := Real.log_le_log (hA o) h
  rw [Real.log_mul (mul_pos (pow_pos (hA _) _) hP).ne' (pow_pos (hA _) _).ne',
    Real.log_mul (pow_pos (hA _) _).ne' hP.ne',
    Real.log_prod (fun x _ => (pow_pos (hA _) _).ne')] at hlog
  simp only [Real.log_pow, Real.log_zpow] at hlog
  have hsum : ∑ x ∈ s, (e x : ℝ) * ((v x : ℝ) * Real.log r) =
      (∑ x ∈ s, (e x : ℝ) * v x) * Real.log r := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  push_cast at hlog
  by_contra hc
  push_neg at hc
  have hm := mul_lt_mul_of_neg_right hc hL
  linarith

end FinPf

end Formalism.L2.Pj.QAt
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangePf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

namespace BasisChangePf

open MvPolynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}

def CB (Q : MvPolynomial ι K) (c : ℝ) : Prop := ∀ μ, ‖AddMonoidAlgebra.coeff Q μ‖ ≤ c

lemma cb_sum {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a ∈ s, CB (g a) c) : CB (∑ a ∈ s, g a) c := by
  classical
  intro μ
  rw [MvPolynomial.coeff_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun a ha => h a ha μ)

lemma cb_mul {Q R : MvPolynomial ι K} {c d : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (hR : CB R d)
    (hd : 0 ≤ d) : CB (Q * R) (c * d) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hQ _) (hR _) (norm_nonneg _) hc

lemma cb_one : CB (1 : MvPolynomial ι K) 1 := by
  classical
  intro μ
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

lemma cb_pow {Q : MvPolynomial ι K} {c : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (n : ℕ) : CB (Q ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact cb_mul (pow_nonneg hc n) ih hQ hc

lemma cb_prod {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) (c : α → ℝ) (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a ∈ s, CB (g a) (c a)) : CB (∏ a ∈ s, g a) (∏ a ∈ s, c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact cb_mul (hc a) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
      (Finset.prod_nonneg fun b _ => hc b)

lemma cb_C_mul (a : K) {Q : MvPolynomial ι K} {c : ℝ} (hQ : CB Q c) : CB (C a * Q) (‖a‖ * c) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hQ μ) (norm_nonneg a)

lemma cb_lin [Fintype ι] (A : ι → ι → K) {c : ℝ} (hc : 0 ≤ c) (hA : ∀ i k, ‖A i k‖ ≤ c) (i : ι) :
    CB (∑ k, C (A i k) * X k) c := by
  classical
  refine cb_sum _ _ hc (fun k _ => fun μ => ?_)
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  calc ‖A i k‖ * ‖AddMonoidAlgebra.coeff (X k : MvPolynomial ι K) μ‖ ≤ ‖A i k‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [MvPolynomial.coeff_X']
        split_ifs <;> simp
    _ ≤ c := by simpa using hA i k

end BasisChangePf

open BasisChangePf in
theorem basisChange_holds : BasisChangeStatement := by
  intro K _ _ ι _ P d hP hP1 A C hC hA μ
  classical
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hL : ∀ i, CB (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k : MvPolynomial ι K) C :=
    fun i => cb_lin A hC0 hA i
  have key : CB (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P) (C ^ d) := by
    conv => arg 1; rw [P.as_sum]

    rw [map_sum]
    refine cb_sum _ _ (pow_nonneg hC0 d) (fun v hv => ?_)
    rw [MvPolynomial.bind₁_monomial]
    have hdeg : v.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (MvPolynomial.mem_support_iff.1 hv)
    have hprod : CB (∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)
        (∏ i ∈ v.support, C ^ v i) :=
      cb_prod _ _ _ (fun i => pow_nonneg hC0 _) (fun i _ => cb_pow hC0 (hL i) (v i))
    have hb := cb_C_mul (AddMonoidAlgebra.coeff P v) hprod
    have hpow : ∏ i ∈ v.support, C ^ v i = C ^ d := by
      rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
      rfl
    intro ν
    calc ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff P v) *
          ∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i) ν‖
        ≤ ‖AddMonoidAlgebra.coeff P v‖ * ∏ i ∈ v.support, C ^ v i := hb ν
      _ ≤ 1 * C ^ d := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_right (hP1 v) (pow_nonneg hC0 d)
      _ = C ^ d := one_mul _
  exact key μ

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBound

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

section Lines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
  {a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)} {th : a.D₀.P.L.Sec}
  {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {jj : ℤ} {n' : ℕ} {La c₁ : ℝ}

theorem CMIn.fin_Tl_ne_zero (s : CMIn a e th jj n' La c₁) : s.Tl.I ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := s.good
  exact h.1

theorem CMIn.fin_line_ne_zero (s : CMIn a e th jj n' La c₁) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    (s.line τ k).I ≠ 0 := by
  letI := H.starRing
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := s.good
  unfold CMIn.line
  cases s.kind τ k with
  | none => exact one_ne_zero
  | some m =>
    have h := s.L_good.2.2.2 m
    show (s.L.ℓ m).I ≠ 0
    revert h
    cases s.L.src m with
    | inl q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h1 q.2).1.1
    | inr q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h2 q.2).1.1

theorem CMIn.fin_count_valLine (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ)
    (w : HeightOneSpectrum (𝓞 K₁)) :
    FractionalIdeal.count K₁ w (s.valLine mo n).I =
      (n : ℤ) * (-FractionalIdeal.count K₁ w s.Tl.I) +
        ∑ x ∈ mo.support, (mo x : ℤ) * (-FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) := by
  classical
  have hT := s.fin_Tl_ne_zero
  have hL : ∀ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v ≠ 0 := fun v => pow_ne_zero _ (s.fin_line_ne_zero _ _)
  show FractionalIdeal.count K₁ w ((s.Tl.I⁻¹) ^ n * (∏ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v)⁻¹) = _
  rw [FractionalIdeal.count_mul K₁ w (pow_ne_zero _ (inv_ne_zero hT))
      (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hL v)),
    FractionalIdeal.count_pow, FractionalIdeal.count_inv, FractionalIdeal.count_inv,
    FractionalIdeal.count_prod K₁ w _ _ (fun v _ => hL v)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_) |>.trans ?_
  · rw [Finsupp.notMem_support_iff.mp hx]; simp
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [FractionalIdeal.count_pow]; ring

end Lines

theorem cfOf_fin_bound : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → 1 ≤ La → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ intAt Xo c a' n la, cfOf d.yF d.μ d.jj F ≠ 0 → -((w.asIdeal.ramificationIdx (𝓞 c.F) : ℝ) * beOf E n' (absA Dw a') la) ≤ (ordAt w (cfOf d.yF d.μ d.jj F) : ℝ) - (FractionalIdeal.count K₁ w (s.valLine d.μ n).I : ℝ) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS _ la w hlw a' n F hF hne
  obtain ⟨Z, gm, lam, A, Bm, ⟨hg0, hg⟩, hlam, ⟨hAB, hA⟩, hbd⟩ :=
    GlobalTheory.T.localArcIntegrality_of_cmNormalisedTrivialisation hK E H Dw l Xo c K₁ d n' La c₁ s hM hS la w hlw a' n
  obtain ⟨P, hPe, hPh⟩ := GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c)
    K₁ d a' n F hF.1
  set m : ℕ := w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la with hm
  have hC1 : (1 : ℝ) ≤ Z.r ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact (one_le_inv₀ (pow_pos Z.r_pos _)).mpr (pow_le_one₀ Z.r_pos.le Z.r_lt.le)
  have hbd' := hbd F hF
  rw [← hPe, FinPf.arcNum_algebraMap] at hbd'
  have key := FinKey.coeff_bound finCore_holds basisChange_holds (GlobalTheory.ArcQ.FinSite.«ι» Z) Z.K₀ Z.res Z.S Z.S_disc Z.S_dense
    Z.S_units P (absA Dw a') hPh n gm hg0 lam (fun τ k => (hlam τ k).1) A Bm hAB _ hC1 hA hbd' d.μ d.jj
  have hcf : cfOf d.yF d.μ d.jj F = (P.coeff d.μ).coeff d.jj := by
    rw [cfOf, ← hPe, FinPf.arcNum_algebraMap]
  rw [hcf] at hne ⊢
  rw [GlobalTheory.ArcQ.FinSite.«norm_ι» Z _ hne, hg] at key
  simp only [Finsupp.prod, (hlam _ _).2] at key
  have hz := FinPf.zpow_bound Z.r Z.r_pos Z.r_lt _ _ n (absA Dw a') m d.μ.support d.μ
    (fun x => -FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) key
  rw [s.fin_count_valLine]
  simp only [beOf, hm] at hz ⊢
  push_cast at hz ⊢
  nlinarith [hz]

end GlobalTheory.ArcCM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBoundStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.cmArcDatum_functional_finite_integrality_bound : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → 1 ≤ La → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ intAt Xo c a' n la, cfOf d.yF d.μ d.jj F ≠ 0 → -((w.asIdeal.ramificationIdx (𝓞 c.F) : ℝ) * beOf E n' (absA Dw a') la) ≤ (ordAt w (cfOf d.yF d.μ d.jj F) : ℝ) - (FractionalIdeal.count K₁ w (s.valLine d.μ n).I : ℝ) := by
  first | exact @GlobalTheory.ArcCM.cfOf_fin_bound | exact GlobalTheory.ArcCM.cfOf_fin_bound | (intros; apply GlobalTheory.ArcCM.cfOf_fin_bound <;> assumption)
end
end
