module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCoStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSectionStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ReachedSectionRegularOnIntegralModelStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScaleStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsExtAllModelsUniformised
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsThetaValData
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueTranslatedProductValuationBound
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortBoundOfTrivAt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamHelp

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToP

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.TermLoc

theorem harmonic_value_ge_local_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hC nab hnab e ρ w n he P hP hloc N hN hu x₂ F hF
  letI := io.toAlgebra
  have hst : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hone : ∀ {Z : Over Xo.X} (t : Z ⟶ Xo.univ.t.G), t ≫ Xo.univ.t.act.act 1 = t := fun t => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hmix := fun b => (GlobalTheory.T.mixed_translate_pullback_eq_reached_section E H Dw l Xo T.Fr (xOf y) N N 1 1 1 1 hN (by simp) (by simp) (by simp)
    (sOf1 y) 1 (x₂ b) (F b) (one_pow _) (hF b).1 (by rw [_root_.mul_one, hone, one_pow]) (by rw [hone, _root_.mul_one]; exact (hF b).1)
    (hF b).2).2
  choose hh hre hpl using hmix
  have hg := fun b => (GlobalTheory.T.regular_section_integral_germ_unique_scale E H Dw l Xo c hst T io y C hC.1 _ (hh b)).1
    (GlobalTheory.T.reachedSection_regular_on_integralModel E H Dw l Xo c hst T io y C hC _ (hh b) (hre b))
  choose f hf using hg
  obtain ⟨B, hB1, -⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hst T io y C
  have hHH : P ∈ HH c w n := hP.1
  have hni := GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies E H Dw l Xo c hst T io y C nab hnab B hB1 _ n hh f hf w P hHH
  have hch := GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hst nab hnab T.Fr y.1 1 1 (N ^ 2 * 1) (N ^ 2) (by simp) (by ring) n hh
    (fun b => sqN Xo N (F b)) hpl w P hHH
  have hn1 : nrm Dw c w (1 : 𝓞 E) = 1 := by simp [nrm]
  rw [hch, hn1, map_one, _root_.one_mul, hni]
  obtain ⟨hF', hA', -, -, -, -, -⟩ := C.gen.1
  obtain ⟨e1, e2, -, -, -, -⟩ := hB1
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF', e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA', e2]
  rw [GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (hloc (N ^ 2 * 1)).trans ?_
  unfold nuLocOf
  refine iInf_le_of_le (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (iInf_le_of_le ?_ le_rfl)
  intro m
  exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

end GlobalTheory.RefSum.TermLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToPStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  first | exact @GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | exact GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | (intros; apply GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThRuleLower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.ThetaBound
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.RefSum.LowP



theorem thRule_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (p : ℕ), p.Prime → ¬ p ∣ l.M → ∀ (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P₁ ∈ harmA (Dw := Dw) c a n, ∀ A B : ℝ, PolyBetween Xo la P₁ A B → ∀ (x : Fin n → Dw.La) (f : Rul Xo c), IsThRule Xo c nab x P₁ f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → (A : EReal) ≤ nval T.V (vV T.V (p : T.Fr)).toNat (evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab p hp hpM la a n P₁ hP₁ A B hPB x f hf T io e ho y hy
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨T', iT, r, y', C', ⟨hr, hiT, φ, hφ, hmap⟩, hfin, hgood, hrat⟩ :=
    Prep.exists_good_chart_allRat E H Dw l Xo c hnab.1 T io y hy (l.M ^ 2) (pow_pos hM0 2)
  have ho' := ho.bc iT hr hiT
  have hvp : 0 < vV T.V (p : T.Fr) := by
    have h1 := ho.2 (p : c.F)
    rw [map_natCast] at h1
    rw [h1]
    exact mul_pos (by exact_mod_cast ho.1) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.vLa_pos la.1 p hp.ne_zero la.2)
  have hvp' : vV T'.V (p : T'.Fr) = (r : ℤ) * vV T.V (p : T.Fr) := by
    rw [← map_natCast iT p, hiT]
  obtain ⟨k₀, hk₀⟩ := Int.eq_ofNat_of_zero_le hvp.le
  have he' : (vV T'.V (p : T'.Fr)).toNat = r * (vV T.V (p : T.Fr)).toNat := by
    rw [hvp', hk₀, ← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  have hk0 : 0 < k₀ := by omega
  have he'pos : 0 < (vV T'.V (p : T'.Fr)).toNat := by
    rw [he', hk₀, Int.toNat_natCast]; exact Nat.mul_pos hr hk0
  have hu : IsUnit (l.M : T'.V) := by
    refine GlobalTheory.PlaceInt.ShortTriv.isUnit_of_coprime T' (ℓ := p)
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)) fun h => ?_
    have h2 := GlobalTheory.PlaceInt.ShortTriv.vV_natCast T' h
    rw [hvp', hk₀] at h2
    have : (0 : ℤ) < (r : ℤ) * (k₀ : ℤ) := by positivity
    omega
  rw [← nval_bc iT hr hiT ((vV T.V (p : T.Fr)).toNat), ← he']
  obtain ⟨n', j, -, -, a3⟩ := (GlobalTheory.TorsFac.factorisation E H Dw l Xo l.M p l.odd dvd_rfl hp).1 hpM
  letI := (iT.comp io).toAlgebra
  choose F hF using fun b : Fin n =>
    (RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).1 hrat (x b)
  have hev : iT (evI y f) = thExpr Xo c nab y'.1 P₁ F := by
    letI : Algebra T.Fr T'.Fr := iT.toAlgebra
    exact GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y T'.Fr φ hφ y'.1 hmap a n x P₁ hP₁ F hF f hf
  have ht : ∀ b, ∃ t' : ptO Xo (xOf y') ⟶ Xo.univ.t.G, t' ^ (l.M ^ 2) = 1 ∧
      IsUUOver Xo.univ.t.G Xo.univ.t.PP l.M (sOf1 y') 1 t' (F b) := by
    intro b
    have h1 : levPt Xo y'.1.x (x b) ^ l.M = 1 := by
      obtain ⟨t', -, -, -, -, b1, b2, -⟩ := hF b
      rw [← b1, ← pow_mul, ← pow_two]
      exact (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1
    obtain ⟨t', -, b2, b3⟩ :=
      (uu_through_moves E H Dw l Xo T'.Fr (xOf y') l.M l.odd (sOf1 y')).2 _ _ (F b) h1 (hF b)
    exact ⟨t', (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1, b3⟩
  choose t' ht1 ht2 using ht
  have hρ : ∀ k, (A : EReal) ≤ nuLocOf C' (vV T'.V (p : T'.Fr)).toNat k (MvPolynomial.map (iT.comp io) P₁) :=
    fun k => (hPB T' (iT.comp io) (r * e) ho' y' hfin C' k).1
  have hb := GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p E H Dw l Xo c T' (iT.comp io) y' C' hgood nab hnab _ A a n he'pos P₁ hP₁ hρ l.M l.odd hu
    t' F (fun b => ⟨ht1 b, ht2 b⟩)
  have hh := (hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P₁).2.2 l.M F
  rw [← hh] at hb
  rw [hev, thExpr, map_inv₀, map_pow, map_natCast, GlobalTheory.PlaceInt.TermBound.nval_inv_pow_mul T' _ _ _ hu]
  exact hb

end GlobalTheory.RefSum.LowP
end
end
end
