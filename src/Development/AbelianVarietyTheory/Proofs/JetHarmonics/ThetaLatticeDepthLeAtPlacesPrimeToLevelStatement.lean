module

public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundOfTwoSteps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShortBasisUniformizationLattice
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniformisedModelIntegralChartAtPointStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCombinationIntegers
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuationStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChartStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHoldStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueTranslatePullbackEqGeneratorStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsValuationClosure
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValue
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveChartsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Mathlib.Tactic.Basify
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShortBasisUniformizationLatticeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.exists_short_basis_uniformization_lattice : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (ho : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (hz : z.IsAlg) (η : T.G.PY j (WeightAlgebra.resCh la)) (hl : T.G.lies j la T' io z η), letI := T.Q.H.starRing; ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G) (ϖ : T'.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 ∧ r ≤ 2 * D.R.f * D.R.m ∧ M0 ≤ 2 * Real.sqrt (2 * D.R.f * D.R.m) ∧ (D.R.m ≤ j → M0 = 0 ∧ Φ = 0) ∧ Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl)) := by
  first | exact @GlobalTheory.ShortBasisAt.exists_shortBasis | exact GlobalTheory.ShortBasisAt.exists_shortBasis | (intros; apply GlobalTheory.ShortBasisAt.exists_shortBasis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.ThetaLeast

theorem iInf_thGen_le_nuLocC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n Dg e : ℕ), 1 ≤ n → 0 < e → DF Dw a ≤ Dg → 4 * Dg + 4 ≤ l.M → (Dg : ℝ) * M0 < l.M → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) ≤ nuLocC C e l.M a n + (((Dg : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab hth T io y C hTr P hP hy ϖ hϖ Q hQ Φ M0 r b hΦ hb hb' α hα hMb hu a n Dg e hn he hD h4 hM0
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
  unfold nuLocC
  refine le_iInf_add_coe fun Pp => le_iInf_add_coe fun hPp => le_iInf_add_coe fun f => le_iInf_add_coe fun hf => ?_
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  obtain ⟨s, cf, Qs, hQs, hsum⟩ := exists_combination_integers c.F T io _ _ n _ _ _ Pp hPp
  have hmap : (∑ i, algebraMap T.Fr F (algebraMap T.V T.Fr (cf i)) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) (Qs i)) = MvPolynomial.map (algebraMap T.Fr F) Pp := by

    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ Dg :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans ((totalDegree_le_DF T hPp).trans hD)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 l.M n f
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    GlobalTheory.T.pointStatements_on_copies_hold.1 E H Dw l Xo c T io y C hTr P hP hy ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α l.M Dg hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin s)
      (fun i => MvPolynomial.map ((algebraMap T.Fr F).comp io) (Qs i))
      (fun i => algebraMap T.Fr F (algebraMap T.V T.Fr (cf i))) (fun i => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f hf ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval]; exact hvx x0 hx0)
  obtain ⟨g, hg, ε, hε, hgv⟩ := GlobalTheory.T.value_translate_pullback_eq_generator' E H Dw l Xo c nab hnab hth T io y C hTr P hP hy ϖ hϖ Q hQ F v hv n D' A' G'
    pD pA pG U' PU oD' hx hact α hα hMb θ θα hθ1 hθ2 hθ3 p w ζ x t₀ t σ' h h1 h2 h3 h4' h5 h6 h7 h8 h9 a (Qs i) (hQs i)
  rw [hgv] at hρ
  have hint : ∀ τ : E →+* ℂ, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ α) := fun τ => by
    obtain ⟨φ, hφ⟩ := exists_lift_integers E T.V T.Fr (io.comp (embF c τ))
    exact ⟨φ α, hφ α⟩
  choose z hz using hint
  have hε' : 0 ≤ v (ε * ∏ τ : E →+* ℂ, algebraMap T.Fr F (io (embK c τ α)) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) := by
    rw [AddValuation.map_mul]
    refine add_nonneg hε ?_
    have := val_algebraMap_nonneg T v hvx (∏ τ : E →+* ℂ, z τ ^ (∑ i : Fin (Dw.mult τ), a (τ, i)))
    simpa only [map_prod, map_pow, hz] using this
  exact (iInf₂_le g hg).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.ThetaLeast
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n Dg e : ℕ), 1 ≤ n → 0 < e → DF Dw a ≤ Dg → 4 * Dg + 4 ≤ l.M → (Dg : ℝ) * M0 < l.M → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) ≤ nuLocC C e l.M a n + (((Dg : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  first | exact @GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC | exact GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC | (intros; apply GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.thetaDepth_le_scaled_rule_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  first | exact @GlobalTheory.DepthRule.depth_le_scaled_value | exact GlobalTheory.DepthRule.depth_le_scaled_value | (intros; apply GlobalTheory.DepthRule.depth_le_scaled_value <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeAtPlacesPrimeToLevel

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthPrimeToLevel

theorem isUnit_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h1 := RPfVal.vLa_int_not_mem la hN
  have h2 : (((N : ℕ) : 𝓞 K) : K) = (N : K) := map_natCast (algebraMap (𝓞 K) K) N
  rw [h2] at h1
  have h3 := ho.2 (N : K)
  rw [h1, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
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

theorem rootDiscriminantDegreeRatio_pos (D : D7) : 0 < rr0 D := by
  unfold rr0
  have h1 : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have h2 : (0 : ℝ) < Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
  positivity

theorem err_le (R N n Dg Φ φ c e g₀ g₁ : ℝ) (hR : 0 < R) (hN : 0 < N) (hn : 0 ≤ n) (he : 0 < e) (hg₀ : 0 < g₀)
    (hg₁ : 1 ≤ g₁) (hΦ0 : 0 ≤ Φ) (hΦ : Φ ≤ e * (R * N ^ 3 * φ))
    (hc : R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g₀ ≤ c) : Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ c * φ := by
  have hφ : 0 ≤ φ := by
    have h1 : 0 ≤ (e * (R * N ^ 3)) * φ := by nlinarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hc hφ)
  calc Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ Dg ^ 2 * (e * (R * N ^ 3 * φ)) / (g₀ * 1) / e := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ := by field_simp
    _ ≤ _ := by
      have h1 : 0 ≤ N ^ 4 * n := by positivity
      have h2 : 0 ≤ N ^ 3 := by positivity
      gcongr
      linarith

theorem depth_le : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro D T h j hj hinj EX w c _ hrun la hg y
  letI := T.Q.H.starRing
  obtain ⟨hlp, hn, h4, hc0, hc⟩ := hrun
  obtain ⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩ := GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ
  obtain ⟨r, Φ, M0, ⟨hΦ0, b, hb1, hb2⟩, -, hM0, hjm, hΦ⟩ :=
    GlobalTheory.T.exists_short_basis_uniformization_lattice D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ
  have hΦ' : Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la y) := hΦ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T.toCore h.toLawsCore.toLawsM EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M T.toCore h.toLawsCore.toLawsM
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨st, hn⟩ := h.nabPin j hj
    have := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
    subst this
    exact hn
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S.V) := by
    refine isUnit_natCast la S _ e ho _ ?_
    rw [hM, Nat.cast_mul]
    intro hm
    rcases la.isPrime.mem_or_mem hm with h1 | h1
    · exact hg 0 h1
    · exact hg 1 h1
  have hf1 : 1 ≤ D.R.f := by
    have h1 := GlobalTheory.DepthLink.finrank_host D
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hm2 := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ w.n := le_trans (Nat.mul_pos (by omega) hr1) hn
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ D.host.g 0 * D.host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by rw [hM]; exact_mod_cast hle
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hDM : (WeightAlgebra.DF w : ℝ) * M0 < (T.Q.l.M : ℕ) := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · exact ((mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)).trans_lt (hc hjm' 0).1).trans_le hle'
    · rw [(hjm hjm').1, mul_zero]; linarith
  have hnum : (WeightAlgebra.DF w : ℝ) ^ 2 * Φ / (T.Q.l.M : ℕ) / e ≤ c * (recPJ h j hj).phiC la y := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · rw [hM, Nat.cast_mul]
      have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
      have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
      exact err_le (rr0 D) _ w.n _ Φ _ c e _ _ (rootDiscriminantDegreeRatio_pos D) (by positivity) (Nat.cast_nonneg _) he' (by linarith)
        (by linarith) hΦ0 hΦ' (hc hjm' 0).2
    · unfold WeightAlgebra.PJ.phiC
      rw [(hjm hjm').2, if_neg (not_lt.2 hjm')]
      simp
  have hA := GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC
    Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ0 hb1 hb2 α hα1 hα2 hMu (wtA w) w.n (WeightAlgebra.DF w) e hn1 ho.1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.DF_wtA_le _ _) (by rw [hM]; exact (h4 0).trans hle) hDM
  have hB := (GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn la).2.2.2.2 S io e ho z hz C
  have hsW := RPfVal.vAdd_sW (recB h.toLawsCore) hinj EX w la hg
  have hs0 : sWt (recB h.toLawsCore) hinj EX w ≠ 0 := by
    refine mul_ne_zero (fun h0 => RPfVal.nnW_not_mem (recB h.toLawsCore) hinj EX w la hg ?_) ?_
    · rw [h0]; exact la.asIdeal.zero_mem
    · have hq : D.host.q.Prime := D.host.hyp.1
      have hd : D.host.d.Prime := D.host.hyp.2.1
      exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
        (pow_ne_zero _ hd.ne_zero))
  have hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤
      (⨅ f ∈ T.th j w, nval S.V e (evI z f)) + (((ramOverZ la : ℝ) * clOf w la : ℝ) : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]
    refine (GlobalTheory.T.thetaDepth_le_scaled_rule_value D T h j hj w hlp _ hs0 la y f hf).trans (le_of_eq ?_)
    exact congrArg (fun x : ℝ => (x : EReal) + vAtV y f) hsW
  have hnu : nusOf (recB h.toLawsCore) w (nuWt T w) la =
      (ramOverZ la : ℝ) * nuWt T w la + (ramOverZ la : ℝ) * clOf w la := by
    unfold nusOf
    rw [dite_eq_right (fun ⟨i, hi⟩ => hg i hi), ← mul_add, ← H1algLink.eWL_eq la]
    rfl
  refine hdep.trans ?_
  rw [hnu, add_right_comm, EReal.coe_add, EReal.coe_add]
  exact add_le_add (hA.trans (add_le_add hB (EReal.coe_le_coe_iff.2 hnum))) le_rfl

end GlobalTheory.DepthPrimeToLevel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeAtPlacesPrimeToLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.thetaLatticeDepth_le_at_places_prime_to_level : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  first | exact @GlobalTheory.DepthPrimeToLevel.depth_le | exact GlobalTheory.DepthPrimeToLevel.depth_le | (intros; apply GlobalTheory.DepthPrimeToLevel.depth_le <;> assumption)
end
end
