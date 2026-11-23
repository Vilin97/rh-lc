module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
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
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLettersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  first | exact @GlobalTheory.ArcQ.evR_arc_isHomogeneous | exact GlobalTheory.ArcQ.evR_arc_isHomogeneous | (intros; apply GlobalTheory.ArcQ.evR_arc_isHomogeneous <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominatorsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  first | exact @GlobalTheory.LetterDenom.main | exact GlobalTheory.LetterDenom.main | (intros; apply GlobalTheory.LetterDenom.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDisc

section

@[expose] public section

namespace GlobalTheory.LetterEval

open GlobalTheory.DiscEval

section General

variable {K : Type} [NormedField K] [CompleteSpace K] {V F : Type} [CommRing V] [Field F]
  (a : V →+* F) (ι : F →+* K) (hi : ∀ v, ‖(ι.comp a) v‖ ≤ 1) {ϖ : V} (hϖ : a ϖ ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)


include hϖ ht0 in
theorem hasSum_laurent_of_mul_eq {q : LaurentSeries F} {g : PowerSeries V} {N : ℕ}
    (h : q * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a g)) :
    HasSum (fun k : ℤ => ι (q.coeff k) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * discEval (ι.comp a) hi ht g) := by
  have h2 : (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.single (N : ℤ) (a ϖ ^ N) := by
    rw [← map_pow, mul_pow, ← map_pow PowerSeries.C, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have h4 : a ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ
  have hc : ∀ n : ℤ, q.coeff n = if n + N < 0 then 0 else
      (a ϖ ^ N)⁻¹ * a (PowerSeries.coeff (n + N).natAbs g) := fun n => by
    have h3 := congrArg (fun g : LaurentSeries F => g.coeff (n + N)) h
    simp only [h2, HahnSeries.coeff_mul_single_add] at h3
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_map] at h3
    split_ifs at h3 ⊢
    · exact (mul_eq_zero.1 h3).resolve_right h4
    · rw [← h3]
      field_simp
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - N := fun k l hkl => by simpa using hkl
  rw [← hinj.hasSum_iff]
  · refine Eq.mpr (congrArg (HasSum · _) (funext fun k => ?_))
      ((hasSum_discEval (ι.comp a) hi ht g).mul_left (((ι (a ϖ) * t) ^ N)⁻¹))
    rw [Function.comp_apply, hc, sub_add_cancel, if_neg (by omega), Int.natAbs_natCast,
      zpow_sub₀ ht0, zpow_natCast, zpow_natCast, map_mul, map_inv₀, map_pow, RingHom.comp_apply,
      mul_pow, mul_inv]
    ring
  · intro n hn
    rw [hc, if_pos, map_zero, zero_mul]
    by_contra h0
    exact hn ⟨(n + N).toNat, by simp only; omega⟩


include hϖ ht0 in
theorem hasSum_lcoeffPoly {σ : Type} (Y : σ → K) {P : MvPolynomial σ (LaurentSeries F)}
    {G : MvPolynomial σ (PowerSeries V)} {N : ℕ}
    (h : P * MvPolynomial.C
        (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ F).comp (PowerSeries.map a)) G) :
    HasSum (fun k : ℤ => MvPolynomial.eval Y (MvPolynomial.map ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G) := by
  classical
  have hμ : ∀ μ, P.coeff μ *
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a (G.coeff μ)) := fun μ => by
    have := congrArg (AddMonoidAlgebra.coeff · μ) h
    rwa [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, mul_comm, MvPolynomial.coeff_map] at this
  set s := P.support ∪ G.support
  have hP : ∀ k : ℤ, GlobalTheory.ArcQ.lcoeffPoly P k =
      ∑ μ ∈ s, MvPolynomial.monomial μ ((P.coeff μ).coeff k) := fun k =>
    Finset.sum_subset Finset.subset_union_left fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  have hG : MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G =
      ∑ μ ∈ s, discEval (ι.comp a) hi ht (G.coeff μ) * ∏ k ∈ μ.support, Y k ^ μ k := by
    rw [MvPolynomial.eval₂_eq]
    exact Finset.sum_subset Finset.subset_union_right fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  rw [hG, Finset.mul_sum]
  simp_rw [← mul_assoc]
  refine Eq.mpr (congrArg (HasSum · _) (funext fun m => ?_))
    (hasSum_sum fun μ (_ : μ ∈ s) =>
      (hasSum_laurent_of_mul_eq a ι hi hϖ ht0 ht (hμ μ)).mul_right (∏ k ∈ μ.support, Y k ^ μ k))

  rw [hP, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_monomial, Finsupp.prod]
  ring

end General

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  intro E _ _ _ H Dw Tv ϖ K _ _ _ ιT hϖ hi t Y ht0 ht hY
  have ht0' : t ≠ 0 := norm_pos_iff.1 ht0
  have hϖ' : algebraMap Tv.V Tv.Fr ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ
  have hϖ'' : ιT (algebraMap Tv.V Tv.Fr ϖ) ≠ 0 := (map_ne_zero ιT).2 hϖ'
  have hi' : ∀ v, ‖(ιT.comp (algebraMap Tv.V Tv.Fr)) v‖ ≤ 1 := hi
  let g : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V) →+* K :=
    MvPolynomial.eval₂Hom (discEval _ hi' ht) Y
  have hgC : ∀ p, g (MvPolynomial.C p) = discEval _ hi' ht p := fun p =>
    MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ x, g (MvPolynomial.X x) = Y x := fun x => MvPolynomial.eval₂Hom_X' _ _ _
  have hϖX : discEval _ hi' ht (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) =
      ιT (algebraMap Tv.V Tv.Fr ϖ) * t := by
    rw [map_mul, discEval_C, discEval_X, RingHom.comp_apply]
  have hu : IsUnit (g (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) := by
    rw [isUnit_iff_ne_zero, map_mul, hgC, hϖX]
    refine mul_ne_zero (mul_ne_zero hϖ'' ht0') ?_
    convert hY using 1
    rw [arcDetR, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    exact hgX _
  let ev : ArcSR Dw Tv.V ϖ →+* K := IsLocalization.Away.lift _ hu
  have hev : ∀ G, ev (algebraMap _ (ArcSR Dw Tv.V ϖ) G) = g G := fun G =>
    IsLocalization.Away.lift_eq _ hu G
  have hevι : ∀ p, ev (arcιR Dw Tv.V ϖ p) = discEval _ hi' ht p := fun p =>
    (hev _).trans (hgC p)
  refine ⟨ev, fun p => ?_, fun x => (hev _).trans (hgX x), fun f N G P hf hP => ?_⟩
  · rw [hevι, ← (hasSum_discEval _ hi' ht p).tsum_eq]
    rfl
  · have hs := hasSum_lcoeffPoly _ ιT hi' hϖ' ht0' ht Y hP
    refine ⟨by simpa using hs.summable.tendsto_cofinite_zero.norm, ?_⟩
    rw [hs.tsum_eq]
    have h1 := congrArg ev hf
    rw [map_mul, map_pow, hevι, hϖX, hev] at h1
    have h2 : (ιT (algebraMap Tv.V Tv.Fr ϖ) * t) ^ N ≠ 0 := pow_ne_zero _ (mul_ne_zero hϖ'' ht0')
    rw [eq_inv_mul_iff_mul_eq₀ h2, mul_comm]
    exact h1

end GlobalTheory.LetterEval
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDiscStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  first | exact @GlobalTheory.LetterEval.exists_eval | exact GlobalTheory.LetterEval.exists_eval | (intros; apply GlobalTheory.LetterEval.exists_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LcoeffPolyConstMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.FrameCut

theorem lcoeffPoly_coeff {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ)
    (μ : ι →₀ ℕ) : (GlobalTheory.ArcQ.lcoeffPoly P m).coeff μ = (P.coeff μ).coeff m := by
  classical
  simp only [GlobalTheory.ArcQ.lcoeffPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; rfl

theorem lcoeffPoly_add {ι K₁ : Type} [Field K₁] (P Q : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (P + Q) m = GlobalTheory.ArcQ.lcoeffPoly P m + GlobalTheory.ArcQ.lcoeffPoly Q m := by
  ext μ
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_add, HahnSeries.coeff_add]

theorem lcoeffPoly_monomial {ι K₁ : Type} [Field K₁] (μ : ι →₀ ℕ) (f : LaurentSeries K₁) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.monomial μ f) m = MvPolynomial.monomial μ (f.coeff m) := by
  classical
  ext ν
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_monomial]
  split_ifs
  · rfl
  · rfl

theorem lcoeffPoly_C_mul_map {ι L : Type} [Field L] (g : LaurentSeries L) (Q : MvPolynomial ι L) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) Q) m =
      MvPolynomial.C (g.coeff m) * Q := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm g,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]

theorem lcoeffPoly_const_mul {ι L : Type} [Field L] (x : L) (P : MvPolynomial ι (LaurentSeries L)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x) * P) m =
      MvPolynomial.C x * GlobalTheory.ArcQ.lcoeffPoly P m := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, lcoeffPoly_coeff,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem exists_subst {ι K₁ L S : Type} [Field K₁] [Field L] [CommRing S] (io : K₁ →+* L)
    (Φ : MvPolynomial ι (LaurentSeries K₁) →+* S) (j : MvPolynomial ι (LaurentSeries L) →+* S)
    (q : ι → MvPolynomial ι L)
    (hC : ∀ f : LaurentSeries K₁, ∃ g : LaurentSeries L, (∀ m, g.coeff m = io (f.coeff m)) ∧
      Φ (MvPolynomial.C f) = j (MvPolynomial.C g))
    (hX : ∀ x, Φ (MvPolynomial.X x) = j (MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (q x)))
    (P : MvPolynomial ι (LaurentSeries K₁)) :
    ∃ P₁ : MvPolynomial ι (LaurentSeries L), j P₁ = Φ P ∧ ∀ m, GlobalTheory.ArcQ.lcoeffPoly P₁ m =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q (GlobalTheory.ArcQ.lcoeffPoly P m) := by
  induction P using MvPolynomial.induction_on' with
  | monomial μ f =>
    obtain ⟨g, hg, hΦ⟩ := hC f
    refine ⟨MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (μ.prod fun x e => q x ^ e), ?_, fun m => ?_⟩
    · rw [MvPolynomial.monomial_eq, map_mul, map_mul, hΦ]
      simp only [Finsupp.prod, map_prod, map_pow, hX]
    · rw [lcoeffPoly_C_mul_map, lcoeffPoly_monomial, MvPolynomial.eval₂Hom_monomial, hg]
      rfl
  | add P Q hP hQ =>
    obtain ⟨P₁, h1, h2⟩ := hP
    obtain ⟨Q₁, h3, h4⟩ := hQ
    exact ⟨P₁ + Q₁, by rw [map_add (f := _), map_add (f := _), h1, h3], fun m => by
      rw [lcoeffPoly_add, lcoeffPoly_add, map_add (f := _), h2, h4]⟩

theorem eval_subst {ι K₁ L K : Type} [Field K₁] [Field L] [Field K] (io : K₁ →+* L) (ιT : L →+* K)
    (q : ι → MvPolynomial ι L) (Y : ι → K) (R : MvPolynomial ι K₁) :
    MvPolynomial.eval Y (MvPolynomial.map ιT (MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q R)) =
      MvPolynomial.eval (fun x => MvPolynomial.eval Y (MvPolynomial.map ιT (q x)))
        (MvPolynomial.map (ιT.comp io) R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval_X]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem arcNum_of_poly {K₁ : Type} [Field K₁] (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :
    arcNum (algebraMap _ (ArcS Dw K₁) P) = P := by
  have hs : ∃ Q, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) Q =
      algebraMap _ (ArcS Dw K₁) P := ⟨P, rfl⟩
  rw [arcNum, dite_eq_left hs]
  exact GlobalTheory.ArcConst.algebraMap_injective Dw K₁ hs.choose_spec

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : Ix Dw → Sˣ)
    (h : ∀ x, t (some x) = 1) : wchar (ex Dw a n) t = (t none : S) ^ n := by
  rw [wchar, Fintype.prod_option]
  simp [h, ex]



theorem frameBound_of_cut (hL : Out.Laws) (hL2 : Out.Laws2) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hev : GlobalTheory.Reg.EvLaws Xo c) {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] {d : ArcDatum Xo c K₁}
    {w : HeightOneSpectrum (𝓞 K₁)} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {Fs : Set (Rul Xo c)}
    (hFs : ∀ F ∈ Fs, F ∈ sec Xo c a n) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr) (hγ : γ ≠ 0)
    (hBc : BcRigidAt Dv γ lam Bm) (hRec : RecordAt Dv Fs) :
    FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs := by
  intro F hF t ht Y hY hdet
  obtain ⟨φ, ψ, z₁, z₂, tγ, hφC, hφX, hψC, hψX, htγ, htγ', hm1, hm2, hb⟩ := hBc
  have hϖ : Dv.ϖ ≠ 0 := Dv.ϖ_irr.ne_zero
  obtain ⟨hdomR, -, -, -, hdiv⟩ := GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators E H Dw Dv.Tv Dv.ϖ hϖ
  have hdom1 := GlobalTheory.ArcConst.isDomain Dw K₁
  have hdom2 := GlobalTheory.ArcConst.isDomain Dw Dv.Tv.Fr
  have hinj := GlobalTheory.ArcConst.algebraMap_injective Dw Dv.Tv.Fr
  have hsec := hFs F hF
  obtain ⟨P, hP, -⟩ := GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters hL hL2 E H Dw l Xo c hev K₁ d a n F hsec
  have e1 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw K₁)).1 _ φ _ _ hm1
  have e2 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcSR Dw Dv.Tv.V Dv.ϖ)).1 _ ψ _ _ hm2
  have e3 := ((GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw Dv.Tv.Fr)).2 hdom2).1 tγ _ _ hb
  rw [wchar_gen a n tγ htγ', e1, e2, htγ, ← hP] at e3
  set f := evR Xo c F Dv.yR with hf
  let q : ArcLt Dw → MvPolynomial (ArcLt Dw) Dv.Tv.Fr := fun x =>
    ∑ l : Fin (Dw.mult x.1), MvPolynomial.X ⟨x.1, x.2.1, l⟩ * MvPolynomial.C (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)
  obtain ⟨P₁, hP₁, hco⟩ := exists_subst Dv.io (φ.toRingHom.comp (algebraMap _ (ArcS Dw K₁)))
    (algebraMap _ (ArcS Dw Dv.Tv.Fr)) q hφC (fun x => by
      refine (hφX x).trans ?_

      simp only [q, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, arcX]) P
  have hγn : γ ^ n ≠ 0 := pow_ne_zero _ hγ
  let P₂ : MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr) :=
    MvPolynomial.C (HahnSeries.C (Γ := ℤ) (γ ^ n)⁻¹) * P₁
  have hP₂ : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₂ = ψ.toRingHom f := by
    have : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₁ = _ := hP₁.trans e3
    simp only [P₂]
    rw [map_mul, this, ← mul_assoc, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      inv_mul_cancel₀ hγn, map_one, map_one, map_one, one_mul]
    rfl
  have hψι : ψ.toRingHom.comp (arcιR Dw Dv.Tv.V Dv.ϖ) =
      (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)) := RingHom.ext fun p => hψC p
  obtain ⟨N, G, hG⟩ := hdiv ψ.toRingHom hψι hψX f ⟨P₂, hP₂⟩
  have hψalg : ψ.toRingHom.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _) =
      (algebraMap _ (ArcS Dw Dv.Tv.Fr)).comp (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)))) := by
    refine MvPolynomial.ringHom_ext (fun p => ?_) (fun x => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      exact hψC p
    · simp only [RingHom.comp_apply, MvPolynomial.map_X]
      exact hψX x
  have hPG : P₂ * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr (PowerSeries.C (R := Dv.Tv.Fr)
      (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))) G := by
    apply hinj
    have h1 := congrArg ψ.toRingHom hG
    have h2 := RingHom.congr_fun hψalg G
    have h3 := RingHom.congr_fun hψι (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ * PowerSeries.X)
    simp only [RingHom.comp_apply] at h2 h3
    rw [h2, map_mul, map_pow, h3, ← hP₂, map_mul (PowerSeries.map _), PowerSeries.map_C, PowerSeries.map_X] at h1
    rw [← h1, map_mul, map_pow]
    rfl
  have hdet0 : (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨ev, hevC, hevX, hevf⟩ := GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc E H Dw Dv.Tv Dv.ϖ Z.K Dv.ιT hϖ Dv.norm_le t Y
    (Z.S_disc t ht).1 (Z.S_disc t ht).2 hdet0
  obtain ⟨hT, hS⟩ := hevf f N G P₂ hG hPG
  have hbd := hRec F hF t ht Y hY hdet ev hevC hevX
  have hq : (fun x => MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (q x))) =
      frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y := by
    funext x

    simp only [q, frameSub, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X,
    MvPolynomial.eval_C, Matrix.map_apply, map_inv₀, Finset.sum_mul, mul_assoc]
  have hterm : ∀ k : ℤ, MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (GlobalTheory.ArcQ.lcoeffPoly P₂ k)) * t ^ k =
      (Dv.ιT γ ^ n)⁻¹ * (MvPolynomial.eval (frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y)
        (MvPolynomial.map Z.ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k) := fun k => by
    simp only [P₂]
    rw [lcoeffPoly_const_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, hco, eval_subst, hq,
      Dv.ιT_io, map_inv₀, map_pow, mul_assoc]
  have hγK : Dv.ιT γ ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hγ)
  rw [← hP, arcNum_of_poly]
  simp only [hterm] at hT hS
  refine ⟨?_, ?_⟩
  · have := hT.const_mul ‖Dv.ιT γ ^ n‖
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← norm_mul, mul_inv_cancel_left₀ hγK]
  · rw [tsum_mul_left] at hS
    rw [← hS]
    exact hbd

theorem frame_of_cut : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Fs : Set (Rul Xo c)), (∀ F ∈ Fs, F ∈ sec Xo c a n) → (∀ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → BcRigidAt Dv γ lam Bm → RecordAt Dv Fs → FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs) ∧ ∀ (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), FinLocalCutAt d w vth vη m Fs → FinLocalAt d w n vth vη m Fs := by
  intro hL hL2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w a n Fs hFs
  refine ⟨fun Z Dv γ lam Bm hγ _ hBc hRec => frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec, ?_⟩
  rintro vth vη m ⟨Z, Dv, γ, lam, A, Bm, ⟨hγ, hγn⟩, hlam, ⟨hAB, hA⟩, hBc, hRec⟩
  refine ⟨Z, Dv.ιT γ, fun τ k => Dv.ιT (lam τ k), fun τ => (A τ).map Dv.ιT, fun τ => (Bm τ).map Dv.ιT,
    ⟨(map_ne_zero _).2 hγ, hγn⟩, fun τ k => ⟨(map_ne_zero _).2 (hlam τ k).1, (hlam τ k).2⟩,
    ⟨fun τ => ?_, fun τ k l => hA τ k l⟩, frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec⟩
  beta_reduce
  rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ArcQ.FrameCut
end
end
end
