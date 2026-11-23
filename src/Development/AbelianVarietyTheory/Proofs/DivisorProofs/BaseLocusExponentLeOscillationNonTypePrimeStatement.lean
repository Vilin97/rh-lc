module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetween
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlopeStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCombinationIntegers
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuationStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTermLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChartStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsValuationClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.NormNum.Parity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelHalfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThRuleLower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRuleBoundedBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundOfTwoSteps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetweenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_harmonicPolynomial_localDepth_between : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  first | exact @GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | exact GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | (intros; apply GlobalTheory.RefSum.GlobalPoly.exists_polyBetween <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
open Limits MonoidalCategory CartesianMonoidalCategory MonObj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory.ThetaLeast

namespace GlobalTheory.RefSum

theorem iInf_thRule_le_nuLocOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), 1 ≤ n → 0 < e → 4 * DF Dw a + 4 ≤ l.M → (DF Dw a : ℝ) * M0 < l.M → ∀ P₁ ∈ harmA (Dw := Dw) c a n, (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V e (evI y f)) ≤ nuLocOf C e l.M (MvPolynomial.map io P₁) + (((DF Dw a : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hy ϖ hϖ Q hQ r Φ M0 hSB α hα hMb hu a n e hn he h4 hM0 P₁ hP₁
  obtain ⟨hΦ, b, hb, hb'⟩ := hSB
  have hth : ThValTot Xo c nab :=
    GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hnab
  letI := io.toAlgebra
  obtain ⟨F, _, _, _, _, _, _, v, hv, hvx⟩ : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F)
      (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v ∧ ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨v, hv⟩ := GlobalTheory.ValClosure.exists_valuation_closure T.V ϖ hϖ
    exact ⟨AlgebraicClosure T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, v, hv⟩
  obtain ⟨TI⟩ := GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart E H Dw l Xo c T io y C P F
  obtain ⟨D', A', G', _, _, pD, pA, pG, U', PU, _, oD', hx, hact, hθ⟩ :=
    (GlobalTheory.T.exists_productData_copies_trivialisation_valuation E H Dw l Xo c T io y C P ϖ hϖ).2 n
  obtain ⟨θ, θα, hθ1, hθ2, hθ3⟩ := hθ F v hv Q hQ α l.M (by have := l.three_le; omega) hα
  have hcop : ∃ u u' : 𝓞 E, u * α + u' * star α = 1 := by
    have h1 := l.coprime
    rw [hMb, Ideal.map_span, Set.image_singleton] at h1
    have h2 : (H.bar : 𝓞 E →+* 𝓞 E) (star α) = α := star_star α
    rw [h2, sup_comm, ← Ideal.span_insert, Ideal.eq_top_iff_one, Ideal.mem_span_pair] at h1
    exact h1
  have hdeg1 : P₁.totalDegree ≤ DF Dw a := by
    have key : ∀ m ∈ P₁.support, (m.sum fun _ e => e) = DF Dw a := by
      intro m hm
      rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => hP₁.1.2.2 m hm τ i
    exact Finset.sup_le fun m' hm' => (key m' hm').le
  unfold nuLocOf
  refine le_iInf_add_coe fun f => le_iInf_add_coe fun hf => ?_
  set Pp : MvPolynomial (LtN Dw n) T.Fr := MvPolynomial.map io P₁ with hPp
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  have hmap : (∑ _i : Fin 1, algebraMap T.Fr F (algebraMap T.V T.Fr 1) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁) = MvPolynomial.map (algebraMap T.Fr F) Pp := by
    rw [Fin.sum_univ_one, map_one, map_one, one_smul, hPp, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ DF Dw a :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdeg1)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 l.M n f
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  have hpoint : RPointT := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
    exact GlobalTheory.SmallTranslate.main h1 h2 h3 h4 h5 GlobalTheory.twistBaseChange_and_valuation_statements.1
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    hpoint E H Dw l Xo c T io y C hTr P hP hy ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α l.M (DF Dw a) hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin 1)
      (fun _ => MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁)
      (fun _ => algebraMap T.Fr F (algebraMap T.V T.Fr 1)) (fun _ => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f hf ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval]; exact hvx x0 hx0)
  obtain ⟨xx, u, hu0, hrel⟩ := GlobalTheory.PtTie.harmonicValue_translate E H Dw l Xo c nab hnab T io y C hTr P hP hy ϖ hϖ Q hQ
    F v hv n D' A' G' pD pA pG U' PU oD' hx hact α l.M rfl hα hMb θ θα hθ2 hθ3 p w ζ x t₀ t (1 * l.M) rfl σ' h
    h1 h2 h3 h4' h6 h7 h8 h9 h5
  obtain ⟨g, hg, -⟩ := existsUnique_thRule Xo c nab hth xx hP₁
  have hgv := hrel a P₁ hP₁ g hg
  rw [hgv, map_mul (algebraMap T.Fr F), ← _root_.mul_assoc] at hρ
  have hint : ∀ τ : E →+* ℂ, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ α) := fun τ => by
    obtain ⟨φ, hφ⟩ := exists_lift_integers E T.V T.Fr (io.comp (embF c τ))
    exact ⟨φ α, hφ α⟩
  choose z hz using hint
  have hε' : 0 ≤ v (u * algebraMap T.Fr F (io (nrm Dw c a α))) := by
    rw [AddValuation.map_mul, hu0, zero_add]
    have := val_algebraMap_nonneg T v hvx (∏ τ : E →+* ℂ, z τ ^ (∑ i : Fin (Dw.mult τ), a (τ, i)))
    simpa only [nrm, map_prod, map_pow, hz] using this
  exact (iInf₂_le g ⟨xx, hg⟩).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.RefSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefAway

theorem vLa_nat_eq_zero {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ}
    (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) : vLa la (N : K) = 0 := by
  rw [vLa, ← map_natCast (algebraMap (𝓞 K) K) N, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 hN]
  simp

theorem vLa_nat_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (h0 : N ≠ 0)
    (hN : ((N : ℕ) : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (N : K) := by
  have h1 : la.valuation K (N : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) N]
    exact (la.valuation_lt_one_iff_mem _).2 hN
  have h2 : la.valuation K (N : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast h0
  have h3 := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at h3
  unfold vLa
  omega

theorem isUnit_nat {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h3 := ho.2 (N : K)
  rw [vLa_nat_eq_zero la hN, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

theorem nat_not_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p N : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime p N) : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at huv
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hp) (la.asIdeal.mul_mem_left _ hN)))

theorem vV_nat_eq {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) (p : ℕ) :
    vV S.V (p : S.Fr) = (e : ℤ) * vLa la (p : K) := by
  rw [← ho.2, map_natCast]

theorem le_nval_place {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) {p : ℕ} (hp : 0 < vLa la (p : K)) (A : ℕ) (x : S.Fr)
    (h : ((A : ℝ) : EReal) ≤ nval S.V (vV S.V (p : S.Fr)).toNat x) :
    (((vLa la (p : K) * A : ℤ) : ℝ) : EReal) ≤ nval S.V e x := by
  by_cases hx : x = 0
  · rw [hx, nval_zero]; exact le_top
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  have h1 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℝ) = (e : ℝ) * (vLa la (p : K) : ℝ) := by
    have h2 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℤ) = (e : ℤ) * vLa la (p : K) := by
      rw [Int.toNat_of_nonneg, vV_nat_eq ho]
      rw [vV_nat_eq ho]; positivity
    exact_mod_cast h2
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hp' : (0 : ℝ) < (vLa la (p : K) : ℝ) := by exact_mod_cast hp
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  rw [h1, le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ he']
  push_cast
  linarith

theorem coprime_type (D : D7) : Nat.Coprime (D.host.g 0 * D.host.g 1) (D.host.QS * D.host.q * D.host.d) := by
  have h (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    have hc := D.ntypes.g_cond k
    have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
    exact h1
  exact Nat.Coprime.mul_left (h 0) (h 1)

theorem err_le (R N ρ u Dg φ c r v g₀ g₁ : ℝ) (hR : 0 ≤ R) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N) (hu : 0 ≤ u) (hr : 0 < r)
    (hv : 0 < v) (hg₀ : 0 < g₀) (hg₁ : 1 ≤ g₁) (hφ : 0 ≤ φ) (hc : R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ ≤ c) :
    Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v) ≤ c * φ / v := by
  have hN : 0 ≤ N := hρ0.trans hρ
  calc Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v)
      ≤ Dg ^ 2 * (R * N ^ 3 * (r * φ)) / (g₀ * 1) / (r * v) := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ / v := by field_simp
    _ ≤ R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ * φ / v := by
      gcongr
      nlinarith [sq_nonneg Dg]
    _ ≤ _ := by gcongr

theorem refExp_le_of_oscLe : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) → ∀ b : ℝ, OscLe (T.Q.Xo j) T.Q.c q (gap (T.Q.Dw j) a) b → refExp_vp (T.U j) cst (wtZ a n) q ≤ (b : EReal) := by
  intro D T hL EX j hj a n cst hD hLP hs hr hJ q hq' hq b hO
  letI := T.Q.H.starRing
  have hqp : q.Prime := hq'.out
  refine (refExp_vp_le_iff _).2 fun la S io e ho y hy φ hφ => ?_
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  obtain rfl := GlobalTheory.PowGerm.starSt _ T.Q.H st hnab.1
  obtain ⟨A, hA⟩ := hO la
  obtain ⟨P₁, hP₁, hPB⟩ := GlobalTheory.T.exists_harmonicPolynomial_localDepth_between D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c q la a hD.1 n hs _ _ hA
  obtain ⟨S', io', y', r, C, P, hy', hr0, hC, hP, hφ', hov, hvm, hsc⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  have ho' := hov la.1 e ho
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T hL EX
  obtain ⟨π, π', hsplit⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hL EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  have hcop : Nat.Coprime q T.Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hqp (D.host.g_prime 0)).2 (hq 0))
      ((Nat.coprime_primes hqp (D.host.g_prime 1)).2 (hq 1))
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S'.V) := isUnit_nat la.1 S' _ _ ho' _ (nat_not_mem la.1 la.2 hcop)
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ n := by omega
  have hρN : ρ ≤ 2 * D.R.f * D.R.m := by
    refine hρ.trans ?_
    rw [GlobalTheory.DepthLink.finrank_host D, (hL.pins.2.2.2 j hj).2.1]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hρN' : (ρ : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hρN
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ T.Q.l.M := hM ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by exact_mod_cast hle
  have hDM : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt ρ) < (T.Q.l.M : ℕ) := by
    refine lt_of_le_of_lt ?_ ((hJ 0).2.1.trans_le hle')
    gcongr

  have hε : 0 < vLa la.1 (q : T.Q.c.F) := vLa_nat_pos la.1 hqp.ne_zero la.2
  have hv0 : 0 < vV S.V (q : S.Fr) := by
    rw [vV_nat_eq ho]
    exact mul_pos (by exact_mod_cast ho.1) hε
  obtain ⟨v, hv⟩ : ∃ v : ℕ, vV S.V (q : S.Fr) = v := ⟨_, (Int.toNat_of_nonneg hv0.le).symm⟩
  have hvpos : 0 < v := by omega
  have hv' : (vV S'.V (q : S'.Fr)).toNat = r * v := by
    rw [hvm q hqp.ne_zero, hv, ← Nat.cast_mul, Int.toNat_natCast]
  have hrv : ((r * v : ℕ) : ℤ) = ((r * e : ℕ) : ℤ) * vLa la.1 (q : T.Q.c.F) := by
    rw [← vV_nat_eq ho', hvm q hqp.ne_zero, hv, Nat.cast_mul]
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos

  have hup := GlobalTheory.RefSum.iInf_thRule_le_nuLocOf _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab S' io' y' C hC P hP hy' ϖ hϖ Q hQ ρ _ _ hSB
    α hα1 hα2 hMu a n (r * v) hn1 (Nat.mul_pos hr0 hvpos) ((hJ 0).1.trans hle) hDM P₁ hP₁
  have hloc := (hPB S' io' _ ho' y' hy' C T.Q.l.M).2
  rw [hv'] at hloc
  have hnum : (DF (T.Q.Dw j) a : ℝ) ^ 2 * (rr0 D * (ρ : ℝ) ^ 3 * (r * φ)) / (T.Q.l.M : ℕ) / ((r * v : ℕ) : ℝ) ≤
      cst * φ / v := by
    rw [hM, Nat.cast_mul, Nat.cast_mul]
    refine err_le (rr0 D) _ ρ _ _ φ cst r v _ _ ?_ (Nat.cast_nonneg _) hρN' ?_ hr0' hvpos' (by linarith) (by linarith)
      hφ.nonneg (hJ 0).2.2
    · unfold rr0; positivity
    · positivity
  have hinf := hup.trans (add_le_add hloc (EReal.coe_le_coe_iff.2 hnum))

  obtain ⟨m, hm, hmlow, -⟩ := GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab _ _ π π' hsplit
    (coprime_type D) a n
  have hdep : depthAt_vp (T.U j) (wtZ a n) q y + ((A : ℝ) : EReal) ≤
      ⨅ (f : Rul (T.Q.Xo j) T.Q.c) (_ : ∃ x : Fin n → (T.Q.Dw j).La, IsThRule (T.Q.Xo j) T.Q.c nab x P₁ f),
        nval S'.V (r * v) (evI y' f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen (T.Q.Xo j) T.Q.c nab a n := ⟨x, P₁, hP₁, hx⟩
    have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1 (hL.unf j hj) nab hnab).2
      a n hD hLP f hf
    have hlow := GlobalTheory.RefSum.LowP.thRule_lower _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab q hqp
      (hqp.coprime_iff_not_dvd.1 hcop) la a n P₁ hP₁ _ _ hPB x f hx
    obtain ⟨s, hs0, hsv, g, hg, hgs⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (wtZ a n)
      ⟨f, hcusp⟩ m hm (hmlow f hf) la.1 (vLa la.1 (q : T.Q.c.F) * A) (by
        rintro _ ⟨⟨_, S₁, io₁, e₁, ho₁, y₁, hy₁, η, hη, rfl⟩, rfl⟩
        exact le_nval_place ho₁ hε A _ (hlow S₁ io₁ e₁ ho₁ y₁ hy₁))
    have h1 : depthAt_vp (T.U j) (wtZ a n) q y ≤ nval S.V v (io s * evI y f) := by
      refine (iInf₂_le g hg).trans (le_of_eq ?_)
      show nval S.V (vV S.V (q : S.Fr)).toNat (evI y (g : Rul (T.Q.Xo j) T.Q.c)) = _
      rw [hv, Int.toNat_natCast, hgs, evI_smul]
    have h2 : nval S'.V (r * v) (io' s) = ((-(A : ℝ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io').2 hs0), ho'.2 s, hsv]
      congr 1
      have h3 : ((r * v : ℕ) : ℝ) = ((r * e : ℕ) : ℝ) * (vLa la.1 (q : T.Q.c.F) : ℝ) := by exact_mod_cast hrv
      have h4 : ((r * v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hr0 hvpos).ne'
      rw [div_eq_iff h4, h3]
      push_cast
      ring
    rw [← hsc nab hnab a n v s f hf, nval_mul, h2] at h1
    refine (add_le_add h1 le_rfl).trans (le_of_eq ?_)
    rw [add_right_comm, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
  have hfin := hdep.trans hinf
  rw [hv, Int.cast_natCast]
  rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_add,
    ← EReal.coe_sub] at hfin
  rw [← EReal.coe_add]
  exact hfin.trans (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.RefAway

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.baseLocusExponent_le_oscillation_nonTypePrime : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) → ∀ b : ℝ, OscLe (T.Q.Xo j) T.Q.c q (gap (T.Q.Dw j) a) b → refExp_vp (T.U j) cst (wtZ a n) q ≤ (b : EReal) := by
  first | exact @GlobalTheory.RefAway.refExp_le_of_oscLe | exact GlobalTheory.RefAway.refExp_le_of_oscLe | (intros; apply GlobalTheory.RefAway.refExp_le_of_oscLe <;> assumption)
end
end
