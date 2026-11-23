module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnPolynomialLocalDepthEqPlaceDepthStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalHarmonicCongrColumnPolynomialStatement
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.DescentPf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Jet

variable {k : Type} [CommRing k] {n : ℕ}

end Jet

section Lin

variable {k : Type} [CommRing k] {n : ℕ}

theorem DpolyN_sub {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ e ∈ S, MvPowerSeries.C (P.coeff e) * DmonN F cp u e g := by
  unfold DpolyN
  refine Finset.sum_subset hS (fun e _ he => ?_)
  have h0 : P.coeff e = 0 := by simpa using he
  rw [h0, map_zero, zero_mul]

theorem DpolyN_addP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P Q : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [DpolyN_sub F cp u (P + Q) g (P.support ∪ Q.support) MvPolynomial.support_add,
    DpolyN_sub F cp u P g (P.support ∪ Q.support) Finset.subset_union_left,
    DpolyN_sub F cp u Q g (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem DpolyN_smulP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (c : k) (P : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (c • P) g = c • DpolyN F cp u P g := by
  rw [DpolyN_sub F cp u (c • P) g P.support MvPolynomial.support_smul,
    DpolyN_sub F cp u P g P.support subset_rfl, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, mul_assoc, ← MvPowerSeries.smul_eq_C_mul]

end Lin

theorem nabValN_addP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (P Q : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (P + Q) = nabValN B k h w0 m f cp u P + nabValN B k h w0 m f cp u Q := by
  unfold nabValN
  rw [DpolyN_addP, map_add (f := _)]

theorem nabValN_smulP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (c : k) (P : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (c • P) = c * nabValN B k h w0 m f cp u P := by
  unfold nabValN
  rw [DpolyN_smulP, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_C]

end Gen

section Asm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

end Asm

section Main

open ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthStableUnderPrimePowPerturbation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PertDepth

theorem nval_neg_eq (T : CDVR) (e : ℕ) (x : T.Fr) : nval T.V e (-x) = nval T.V e x := by
  by_cases hx : x = 0
  · subst hx; rw [neg_zero]
  · rw [nval_of_ne (neg_ne_zero.2 hx), nval_of_ne hx]
    simp only [vV, Valuation.map_neg]

theorem iInf_nval_add_eq (T : CDVR) (e : ℕ) {ι : Type*} (Q : ι → Prop) (A D : ι → T.Fr) (M : EReal)
    (hD : ∀ i, Q i → M ≤ nval T.V e (D i)) (hA : ⨅ (i) (_ : Q i), nval T.V e (A i) < M) :
    ⨅ (i) (_ : Q i), nval T.V e (A i + D i) = ⨅ (i) (_ : Q i), nval T.V e (A i) := by
  set Y := ⨅ (i) (_ : Q i), nval T.V e (A i) with hY
  set X := ⨅ (i) (_ : Q i), nval T.V e (A i + D i) with hX
  have hge : min Y M ≤ X := le_iInf₂ fun i hi =>
    le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) (nval_add e (A i) (D i))
  have hle : min X M ≤ Y := le_iInf₂ fun i hi => by
    have h1 := nval_add (V := T.V) e (A i + D i) (-D i)
    rw [add_neg_cancel_right, nval_neg_eq] at h1
    exact le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) h1
  have h1 : Y ≤ X := by rwa [min_eq_left hA.le] at hge
  have h2 : X ≤ Y := by
    rcases le_total X M with h | h
    · rwa [min_eq_left h] at hle
    · rw [min_eq_right h] at hle; exact absurd (lt_of_le_of_lt hle hA) (lt_irrefl _)
  exact le_antisymm h2 h1

theorem nval_pow_p (T : CDVR) (p e : ℕ) (he : 0 < e) (hp : vV T.V (p : T.Fr) = e) (N : ℕ) :
    nval T.V e ((p : T.Fr) ^ N) = ((N : ℝ) : EReal) := by
  have hp0 : (p : T.Fr) ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp [vV] at hp
    omega
  have h1 : nval T.V e (p : T.Fr) = ((1 : ℝ) : EReal) := by
    rw [nval_of_ne hp0, hp]
    congr 1
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    push_cast
    field_simp
  induction N with
  | zero =>
    rw [pow_zero, nval_of_ne one_ne_zero]
    simp [vV]
  | succ N ih =>
    rw [pow_succ, nval_mul, ih, h1, ← EReal.coe_add]
    push_cast
    rfl

end GlobalTheory.PertDepth


open GlobalTheory.PertDepth in
theorem GlobalTheory.nuLocOf_pert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p T io y Ch e he hp a n N k ρ B P₀ R hCh hR hP₀ hBN
  letI := io.toAlgebra
  have hRv : ∀ f : PS T.Fr n Ch.ch.d, IsIntPS T f →
      ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ => ℓ.2.2)
        (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) R) := by
    intro f hf
    have h1 := hCh k
    rw [nuLocC_eq_iInf] at h1
    exact le_trans h1 (le_trans (iInf₂_le R hR) (iInf₂_le f hf))
  unfold nuLocOf
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_addP, Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_smulP]
  refine iInf_nval_add_eq T e _ _ _ (((N : ℝ) - ρ : ℝ) : EReal) (fun f hf => ?_) ?_
  · rw [nval_mul, nval_pow_p T p e he hp N]
    have := add_le_add (le_refl ((N : ℝ) : EReal)) (hRv f hf)
    rw [← EReal.coe_add] at this
    simpa [sub_eq_add_neg] using this
  · refine lt_of_le_of_lt hP₀ ?_
    exact EReal.coe_lt_coe_iff.2 (by linarith)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthStableUnderPrimePowPerturbationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  first | exact @GlobalTheory.nuLocOf_pert | exact GlobalTheory.nuLocOf_pert | (intros; apply GlobalTheory.nuLocOf_pert <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetween

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.GlobalPoly

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ v.asIdeal) : 0 < vLa v (p : K) := by
  have hne : (p : K) ≠ 0 := by exact_mod_cast hp0
  have hlt : v.valuation K (p : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hp
  have h0 : v.valuation K (p : K) ≠ 0 := by simpa using hne
  have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
  simp only [WithZero.log_one] at this
  simp only [vLa]; omega

theorem vV_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
  simp [vV, this]

theorem vV_prime_le (T : CDVR) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hv : 0 < vV T.V (p : T.Fr)) :
    vV T.V (q : T.Fr) ≤ vV T.V (p : T.Fr) := by
  by_cases hpq : q = p
  · subst hpq; exact le_rfl
  have hcop : IsCoprime ((q : ℤ)) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hpq)
  have hcopV : IsCoprime ((q : T.V)) (p : T.V) := by
    simpa using hcop.map (Int.castRingHom T.V)
  have hpm : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    by_contra h
    have hu : IsUnit (p : T.V) := by
      by_contra h'; exact h ((IsLocalRing.mem_maximalIdeal _).2 h')
    have := vV_of_isUnit T hu
    rw [map_natCast] at this; omega
  have hqu : IsUnit (q : T.V) := by
    by_contra h'
    have hqm : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := (IsLocalRing.mem_maximalIdeal _).2 h'
    obtain ⟨u, w, huw⟩ := hcopV
    have h1 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      rw [← huw]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqm) (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := vV_of_isUnit T hqu
  rw [map_natCast] at this
  rw [this]; exact hv.le

end GlobalTheory.RefSum.GlobalPoly

theorem GlobalTheory.RefSum.GlobalPoly.exists_polyBetween : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn A B hNu
  obtain ⟨N, hN⟩ := exists_nat_gt (B + ∑ q ∈ D.host.condN.primeFactors,
    1 * D.host.vdH q * ((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2)
  obtain ⟨P₁, hP₁, hglob⟩ := GlobalTheory.T.exists_global_harmonic_congr_column_polynomial D.host.E H Dw l Xo c p la a ha n hn N
  refine ⟨P₁, hP₁, fun T io e ho y hy Ch k => ?_⟩
  obtain ⟨Bc, R, hcols, hR, heq⟩ := hglob T io e ho
  have hchoice := GlobalTheory.T.columnPolynomial_localDepth_eq_placeDepth D.host.E H Dw l Xo c p la T io e ho y Ch (gap Dw a) n Bc hcols k
  have hv : 0 < vV T.V (p : T.Fr) := by
    rw [← map_natCast io p, ho.2]
    exact mul_pos (by exact_mod_cast ho.1) (GlobalTheory.RefSum.GlobalPoly.vLa_pos_of_mem la.1 hp.out.ne_zero la.2)
  have hve : vV T.V (p : T.Fr) = ((vV T.V (p : T.Fr)).toNat : ℤ) := (Int.toNat_of_nonneg hv.le).symm
  have he : 0 < (vV T.V (p : T.Fr)).toNat := by omega
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D H Dw l Xo c (fun _ => rfl) T io y Ch _ he a n
    (Formalism.L2.Pj.DF Dw a) le_rfl
  have hNu' := hNu T io e ho y
  have hpert := GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation D.host.E H Dw l Xo c p T io y Ch _ he hve a n N k _ B (polyT Bc (gap Dw a)) R hch hR
    (hchoice.trans_le (hNu'.2 hy)) (by
      refine lt_of_le_of_lt (add_le_add le_rfl (Finset.sum_le_sum fun q hq => ?_)) hN
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hle := GlobalTheory.RefSum.GlobalPoly.vV_prime_le T hp.out hqp hv
      have hr : (vV T.V (q : T.Fr) : ℝ) / ((vV T.V (p : T.Fr)).toNat : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast he)]
        rw [hve] at hle
        exact_mod_cast hle
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr (D.host.vdH_nonneg q)) (Nat.cast_nonneg _)) zero_le_two)
  rw [heq, hpert, hchoice]
  exact ⟨hNu'.1, hNu'.2 hy⟩
end
end
