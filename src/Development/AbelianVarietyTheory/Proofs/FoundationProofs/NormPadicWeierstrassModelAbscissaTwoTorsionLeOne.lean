module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoundMeansPosLogAreaNormalisedTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneEvenNormUnitAtTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulByIntegralIsClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstMulLogEqNSer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOrderParameterSeriesBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
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
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointLocalHeightEqOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.Nonarchimedean.Completion

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateProductSigmaStarPowLatticeLaw

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ThetaLaw

open GlobalTheory.ThetaParam

theorem pull_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  intro Λ hΛ t₀ ht y N hy ω hω z
  have hlaw : ∀ x ∈ Λ, ∀ v, sgStar Λ (v + x) = (if x / 2 ∈ Λ then 1 else -1) * sgStar Λ v *
      Complex.exp ((Real.pi : ℂ) * v * (starRingEnd ℂ) x / (area Λ : ℂ) +
        (Real.pi : ℂ) * x * (starRingEnd ℂ) x / (2 * (area Λ : ℂ))) := by
    intro x hx v
    have e := hΛ.sg_law hx v
    simp only [U1] at e
    rw [← e, mul_assoc, ← Complex.exp_add]
    ring_nf
    simp
  have hne : ∃ z, sgStar Λ z ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1
    rw [show sgStar Λ = fun _ => 0 from funext h] at hd
    simp at hd
  have hsl : ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
    fun ω hω z => hΛ.sg_law hω z
  have hx : (N : ℂ) * ω ∈ Λ := by simpa [nsmul_eq_mul] using nsmul_mem hω N
  have c1 : cocy Λ ((N : ℂ) * ω) y ^ 2 = 1 := by
    have e := cocy_pow Λ ω y N 1
    have r := cocy_root (m := 1) (n := N) hne hsl (by simpa using hω) hy
    simp only [Nat.cast_one, one_mul, mul_one] at e r
    rw [e, ← pow_mul, r]
  have c2 : cocy Λ ((N : ℂ) * ω) t₀ ^ 4 = 1 := by
    have r := cocy_root (m := 1) (n := 2) hne hsl (a := (N : ℂ) * ω) (b := t₀) (by simpa using hx) (by simpa using ht)
    simpa using r
  have hψ : ∀ x : ℂ, (if x / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro x; split_ifs <;> norm_num
  have hprod : ∀ v, U1 Λ y (GL3Theta.th0 Λ t₀) v * GL3Theta.th0 Λ t₀ v =
      sgStar Λ (v + y + t₀) * sgStar Λ (v + t₀) *
        (Complex.exp (-(Real.pi : ℂ) * (v + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) /
        (U1 Λ t₀ (sgStar Λ) 0) ^ 2 := by
    intro v
    simp only [GL3Theta.th0, U1]
    ring
  have hE : Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + y + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω) + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) =
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) *
      (cocy Λ ((N : ℂ) * ω) y ^ 2 * cocy Λ ((N : ℂ) * ω) t₀ ^ 4) := by
    simp only [cocy, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_add (f := _), map_natCast]
    push_cast
    ring
  rw [c1, c2, mul_one, mul_one] at hE
  rw [hprod, hprod,
    show (N : ℂ) * (z + ω) + y + t₀ = ((N : ℂ) * z + y + t₀) + (N : ℂ) * ω by ring,
    show (N : ℂ) * (z + ω) + t₀ = ((N : ℂ) * z + t₀) + (N : ℂ) * ω by ring,
    hlaw _ hx, hlaw _ hx, hlaw _ hω z, mul_pow, mul_pow, pow_mul (if ω / 2 ∈ Λ then (1 : ℂ) else -1) 2 (N ^ 2), hψ ω, one_pow, one_mul]
  linear_combination (sgStar Λ ((N : ℂ) * z + y + t₀) * sgStar Λ ((N : ℂ) * z + t₀) * sgStar Λ z ^ (2 * N ^ 2) /
      (U1 Λ t₀ (sgStar Λ) 0) ^ 2) * ((if (N : ℂ) * ω / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 * hE +
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) * hψ ((N : ℂ) * ω))

end GlobalTheory.ThetaLaw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateProductSigmaStarPowLatticeLawStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTranslateProduct_sigmaStarPow_lattice_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  first | exact @GlobalTheory.ThetaLaw.pull_law | exact GlobalTheory.ThetaLaw.pull_law | (intros; apply GlobalTheory.ThetaLaw.pull_law <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicWeierstrassModelAbscissaTwoTorsionLeOne

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.PullBackSplit
open GlobalTheory.EvenTheta

section
variable {p : ℕ} [Fact p.Prime]

theorem int_mulBy_of_closure (g : GL3Theta.G1 p) (hok : g.Ok) {c : ℂ_[p]}
    (hc : c ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[p]))) :
    IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  refine closure_minimal (t := {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])})
    ?_ (GlobalTheory.mulBy_integral_isClosed p g) hc
  rintro _ ⟨n, rfl⟩
  show IntegralMv _
  rw [GlobalTheory.SerTransport.mulBy_X]
  exact intSer_iff.2 ((GlobalTheory.IntDLog.int_dlog p g hok).2.2 n)

theorem neg_one_mem_closure : (-1 : ℂ_[p]) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[p])) := by
  have h1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).sub_const 1
  rw [zero_sub] at h2
  refine mem_closure_of_tendsto h2 (Filter.Eventually.of_forall fun n => ⟨p ^ n - 1, ?_⟩)
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)]
  simp

theorem int_of_mul_reflect {f m : PowerSeries ℂ_[p]} (hf : BddSer f) (hm : IntSer m)
    (hm0 : PowerSeries.constantCoeff m = 0)
    (hmm : (PowerSeries.subst m (PowerSeries.subst m f : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p]) = f)
    (h : IntSer (f * PowerSeries.subst m f)) : IntSer f := by
  have hS := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.2.2.1
  obtain ⟨B, hB⟩ := hf
  intro n
  by_contra hn
  push Not at hn
  have h1 := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p f _ 1 ⟨B, hB⟩ ⟨B, hS f m B hB hm hm0⟩ h n
  have h2 := hS (PowerSeries.subst m f) m 1 (fun j => by
    nlinarith [h1 j, norm_nonneg (PowerSeries.coeff j (PowerSeries.subst m f : PowerSeries ℂ_[p]))]) hm hm0 n
  rw [hmm] at h2
  linarith

theorem IntSer.pow {f : PowerSeries ℂ_[p]} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, ← map_one PowerSeries.C]; exact int_C (by simp)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem translate_sigma_star_neg {Λ : AddSubgroup ℂ} (h : IsLat Λ) (v z : ℂ) :
    U1 Λ v (sgStar Λ) (-z) = -U1 Λ (-v) (sgStar Λ) z := by
  simp only [U1]
  rw [show -z + v = -(z + -v) by ring, h.sg_neg, map_neg, neg_mul]
  congr 3 <;> ring

end

theorem norm_padicWeierstrassModelAbscissa_twoTorsion_le_one (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (t0 : ℂ) (ht0 : GL3Theta.IsTwoTorsionPointUnkilled D g.abelian₂ t0) : ‖xAt g t0‖ ≤ 1 := by
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hnm : t0 ∉ g.abelian₂ := GlobalTheory.PositiveMeans.not_mem_lattice_of_isCMTorsionBasePoint ht0 hst
  by_cases hp : p = 2
  · subst hp
    obtain ⟨a, β, k, ha, hβ, hn, htrc, hN, hb⟩ := GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two D g.lam
    obtain ⟨hb1, hb2⟩ := hb _ _ ht0
    have hst' : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := fun ω hω => ha ▸ hst a ω hω
    have hlat' : IsLat g.abelian₂ := hlat
    have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
      have := hlat'.differentiable
      unfold U1
      fun_prop, huse x hx⟩
    have hint := int_mulBy_of_closure g hok
      (GlobalTheory.TwoAdicFirst.fst_mem_closure_natCast D g.lam _ (subset_closure ⟨a, rfl⟩))
    simp only [GL3Theta.tauK, ha] at hint
    exact (int_th hok hlat' hdisc h2 h3 (fun t h h' => (hwp t h h').1) halg hnm ht0.1 hβ hn hst' htrc hN
      hb1 hb2 hint).2
  · exact GlobalTheory.TorsionAbscissa.norm_xAt_le D p cc δ g hg' t0 ⟨hnm, 2, two_pos,
      (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp), by exact_mod_cast ht0.1⟩

theorem pull_back_split : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D g.abelian₂ t0 → ∀ (y : ℂ) (N : ℕ), 0 < N → (N : ℂ) * y ∈ g.abelian₂ → p ∣ N → SplitIn D p → ∃ h : PowerSeries ℂ_[p], (∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) ∧ g.atU (fun z => U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0) ((N : ℂ) * z)) = h * g.atU (fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z)) := by
  intro D hI p _ cc δ g hg t0 ht0 y N hN hNy _ hsp
  have hθ := intSer_iff.1 ((GlobalTheory.ThetaParam.theta_param_integral D hI p cc δ g hg t0 ht0).2 hsp).1
  have hx0 := norm_padicWeierstrassModelAbscissa_twoTorsion_le_one D p cc δ g hg t0 ht0
  have hht := GlobalTheory.T.torsionPoint_localHeight_eq_one D p cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have ht0n : t0 ∉ g.abelian₂ := GlobalTheory.PositiveMeans.not_mem_lattice_of_isCMTorsionBasePoint ht0 hst
  have ht2 : ((2 : ℕ) : ℂ) * t0 ∈ g.abelian₂ := by exact_mod_cast ht0.1
  have hq0 : InRationalLattice g.abelian₂ t0 := ⟨2, two_pos, ht2⟩
  have hT := GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt g.abelian₂ hlat' halg t0 ht0n ht0.1
  have hth := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties g.abelian₂ hlat' t0 ht0n ht0.1
  have hAy : AlgEnt (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)) := (hT y ⟨N, hN, hNy⟩).1
  have hA0 : AlgEnt (GL3Theta.th0 g.abelian₂ t0) := by
    have h0 := (hT 0 (rational_lattice_point_zero _)).1
    rwa [thetaTranslation_zero] at h0
  have hσ : AlgEnt (sgStar g.abelian₂) := by
    have h0 := halg 0 (rational_lattice_point_zero _)
    rwa [thetaTranslation_zero] at h0
  have hSR := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  have hTr := GlobalTheory.SerTransport.transport p g
  obtain ⟨hε, hw, hw0, hE, hσU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hd := fun v hv hq => GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hσ v hv (hwp v hq hv).1
  set E := ePhi1 g.lam g.abelian₂ g.C g.wq with hEdef

  have hE2 : IntSer (E ^ 2) := by
    have hf2 : g.atU (GL3Theta.th0 g.abelian₂ t0) ^ 2 = E ^ 2 * lineSer g.wq⁻¹ (xAt g t0) := by
      rw [← (atU_sq g hA0).2, ← (hd t0 ht0n hq0).2]
      exact congrArg _ (funext hth.2.2.2.1)
    have h0 : PowerSeries.constantCoeff (lineSer g.wq⁻¹ (xAt g t0)) = 1 := by
      simp only [lineSer, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, hw0]; simp
    have := hθ.sq.mul (((int_line hw).2 hx0).inv (by rw [h0, norm_one]))
    rwa [hf2, mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [h0]; exact one_ne_zero), mul_one] at this

  obtain ⟨h, hh, hh0, -, htr⟩ := hTr.2.2.2 hok (N : ℂ) (natCast_mem _ N)
  obtain ⟨m, hm, hm0, -, hmr⟩ := hTr.2.2.2 hok (-1 : ℂ) (neg_mem (one_mem _))
  have hhint : IntSer h := by
    refine intSer_iff.1 (hh ▸ int_mulBy_of_closure g hok (subset_closure ⟨N, ?_⟩))
    rw [lamC_coe _ (natCast_mem _ N)]
    exact (map_natCast g.lam N).symm
  have hmint : IntSer m := intSer_iff.1 (hm ▸ int_mulBy_of_closure g hok (by
    rw [lamC_neg_one]; exact neg_one_mem_closure))
  obtain ⟨hF, -⟩ := htr _ hAy
  obtain ⟨hTa, hTe⟩ := htr _ hA0
  set A := U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0) with hA
  set T := g.atU (fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z)) with hTdef
  have hTint : IntSer T := by rw [hTe]; exact hSR.2.2.2.2.2.1 _ h 1 hθ hhint hh0
  have hT0 : PowerSeries.constantCoeff T = 1 := by
    rw [hTdef, (hTr.2.2.1 _ hTa).2, mul_zero, hth.2.1, lamC_one]
  have hTi : T⁻¹ * T = 1 := PowerSeries.inv_mul_cancel _ (by rw [hT0]; exact one_ne_zero)
  have hTinv := hTint.inv (by rw [hT0, norm_one])
  set F := g.atU (fun z => A ((N : ℂ) * z)) with hFdef
  suffices hFint : IntSer F from ⟨F * T⁻¹, hFint.mul hTinv, by rw [mul_assoc, hTi, mul_one]⟩

  have hFb : BddSer F := by
    obtain ⟨h1, h2'⟩ := atU_mul g hF hTa
    obtain ⟨B, hB, hBe⟩ := GlobalTheory.T.thetaOrder_parameterSeries_bounded p g hok hlat' h2 h3 hdisc hσ t0 ht0n (hwp t0 hq0 ht0n).1 (2 * N ^ 2) _ h1
      (GlobalTheory.T.thetaTranslateProduct_sigmaStarPow_lattice_law g.abelian₂ hlat' t0 ht0.1 y N hNy)
    rw [h2', pow_mul] at hBe
    have := ((IntSer.pow hE2 (N ^ 2)).bdd.mul hB).mul hTinv.bdd
    rwa [← hBe, mul_assoc, mul_comm T, hTi, mul_one] at this

  have hAm := (hmr _ hAy).1
  have hG2 : IntSer (g.atU (fun w => A w * A (-1 * w))) := by
    set c := U1 g.abelian₂ t0 (sgStar g.abelian₂) 0 with hc
    have hcQ : c ∈ Qbar := (hTr.2.2.1 _ (halg t0 hq0)).1
    have hcn : ‖lamC g.lam c‖ = 1 := by
      have := hht t0 hq0 ht0n
      rw [max_eq_left hx0, mul_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
    have hr := GlobalTheory.ThetaParam.cocy_root ⟨t0, (hlat'.sg_eq_zero t0).not.2 ht0n⟩
      (fun ω hω => hlat'.sg_law hω) hNy ht2
    have hm' : 0 < N * 2 * 2 := by positivity
    set κ := c⁻¹ * GlobalTheory.ThetaParam.cocy g.abelian₂ y t0 with hκ
    have hκQ : κ ∈ Qbar := mul_mem (inv_mem hcQ) (GlobalTheory.ThetaParam.root_mem hm' hr)
    have hκn : ‖lamC g.lam κ‖ = 1 := by
      rw [hκ, lamC_mul _ (inv_mem hcQ) (GlobalTheory.ThetaParam.root_mem hm' hr), norm_mul,
        GlobalTheory.ThetaParam.norm_lamC_inv _ hcQ hcn, GlobalTheory.ThetaParam.norm_lamC_root _ hm' hr, one_mul]
    have hU : ∀ z, A z = κ * U1 g.abelian₂ (y + t0) (sgStar g.abelian₂) z := by
      intro z
      have hth' : GL3Theta.th0 g.abelian₂ t0 = fun z => c⁻¹ * U1 g.abelian₂ t0 (sgStar g.abelian₂) z := by
        funext z
        rw [GL3Theta.th0, div_eq_inv_mul]
      rw [hA, hth', GlobalTheory.ThetaParam.thetaTranslation_const_mul]
      beta_reduce
      rw [GlobalTheory.ThetaParam.thetaTranslation_comp_eq_cocycle_mul, hκ, mul_assoc]
    have hqv : InRationalLattice g.abelian₂ (y + t0) := by
      refine ⟨N * 2, by positivity, ?_⟩
      have := add_mem (nsmul_mem hNy 2) (nsmul_mem ht2 N)
      convert this using 1
      simp only [nsmul_eq_mul]
      push_cast
      ring
    by_cases hv : y + t0 ∈ g.abelian₂
    · have e : (fun w => A w * A (-1 * w)) = fun w => ((-1) * (κ * κ)) * sgStar g.abelian₂ w ^ 2 := by
        funext w
        rw [hU, hU, hlat'.sg_law hv, hlat'.sg_law hv, neg_one_mul, hlat'.sg_neg]
        split_ifs <;> ring
      have hq := mul_mem (neg_mem (one_mem Qbar)) (mul_mem hκQ hκQ)
      rw [e, (atU_smul g hq (atU_sq g hσ).1).2, (atU_sq g hσ).2, hσU, mul_pow]
      refine (int_C ?_).mul (((int_C hε.le).mul int_X).sq.mul hE2)
      rw [lamC_mul _ (neg_mem (one_mem Qbar)) (mul_mem hκQ hκQ), lamC_mul _ hκQ hκQ, lamC_neg_one]
      simp [hκn]
    · set s := U1 g.abelian₂ (y + t0) (sgStar g.abelian₂) 0 with hs
      have hsQ : s ∈ Qbar := (hTr.2.2.1 _ (halg _ hqv)).1
      have e : (fun w => A w * A (-1 * w)) = fun w => ((κ * s) * (κ * s)) * sqTh g.abelian₂ (y + t0) w := by
        funext w
        have e1 := hlat'.sqTh_mul hv w
        have e2 := translate_sigma_star_neg hlat' (y + t0) 0
        rw [neg_zero] at e2
        rw [hU, hU, neg_one_mul, translate_sigma_star_neg hlat']
        linear_combination κ ^ 2 * e1 - κ ^ 2 * s * sqTh g.abelian₂ (y + t0) w * e2
      have hq := mul_mem hκQ hsQ
      have hh1 := hht _ hqv hv
      have hn : ‖lamC g.lam ((κ * s) * (κ * s))‖ = ‖GlobalTheory.ThetaTransl.cval g (y + t0)‖ ^ 2 := by
        rw [lamC_mul _ hq hq, lamC_mul _ hκQ hsQ, norm_mul, norm_mul, hκn, one_mul, _root_.sq]; rfl
      rw [e, (atU_smul g (mul_mem hq hq) (hd _ hv hqv).1).2, (hd _ hv hqv).2, mul_left_comm, lineSer, mul_sub,
        ← mul_assoc (PowerSeries.C _), ← map_mul]
      have hp := pow_nonneg (norm_nonneg (GlobalTheory.ThetaTransl.cval g (y + t0))) 2
      refine hE2.mul (((int_C ?_).mul hw).sub ((int_C ?_).mul int_X.sq))
      · rw [hn]
        nlinarith [le_max_left 1 ‖xAt g (y + t0)‖]
      · rw [norm_mul, hn]
        nlinarith [le_max_right 1 ‖xAt g (y + t0)‖]
  obtain ⟨hF', hF'e⟩ := hmr _ hF
  refine int_of_mul_reflect hFb hmint hm0 ?_ ?_
  · rw [← hF'e, ← (hmr _ hF').2, hFdef]
    congr 1
    funext z
    congr 1
    ring
  · have := hSR.2.2.2.2.2.1 _ h 1 hG2 hhint hh0
    rw [← (htr _ (atU_mul g hAy hAm).1).2] at this
    rw [← hF'e, hFdef, ← (atU_mul g hF hF').2]
    have e : (fun z : ℂ => A ((N : ℂ) * z) * A ((N : ℂ) * (-1 * z))) =
        fun z : ℂ => A ((N : ℂ) * z) * A (-1 * ((N : ℂ) * z)) := by
      funext z
      rw [mul_left_comm (N : ℂ)]
    rw [e]
    exact this

end GlobalTheory.PullBackSplit
end
end
end
