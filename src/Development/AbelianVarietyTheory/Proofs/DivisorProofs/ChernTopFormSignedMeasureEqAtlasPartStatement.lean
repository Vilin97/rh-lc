module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbarStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityChernPolynomialReEqChernPolyTopDensity

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTopDens

variable {n : ℕ}

theorem coeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) (d : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun y => C c * X y) Q) d = c ^ (d.sum fun _ e => e) * AddMonoidAlgebra.coeff Q d := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    have : aeval (fun y => C c * X y) (monomial u a) = monomial u (c ^ (u.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq]
      rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, C_mul, map_prod]
      simp only [map_pow]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

section Rev

variable {r : Type} [Fintype r] [DecidableEq r]

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix r r A) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem charpolyRev_smul {A : Type} [CommRing A] (c : A) (M : Matrix r r A) :
    (c • M).charpolyRev = M.charpolyRev.comp (Polynomial.C c * Polynomial.X) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem aeval_chernPoly (c : ℂ) (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) :
    aeval (fun y => C c * X y) (chernPoly G v k) = c ^ k • chernPoly G v k := by
  let ψ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
    (aeval fun y => C c * X y : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ).toRingHom
  have e : ∀ p, aeval (fun y => C c * X y) p = ψ p := fun _ => rfl
  have hM : (-curvPoly G v).map ψ = (C c : MvPolynomial (Fin n × Fin n) ℂ) • (-curvPoly G v) := by
    refine Matrix.ext fun i j => ?_

    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, curvPoly, Matrix.of_apply, map_neg, map_sum,
    map_mul, smul_eq_mul, Finset.mul_sum, mul_neg, ← e, aeval_X, aeval_C, algebraMap_eq]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    ring
  unfold chernPoly
  rw [e, ← Polynomial.coeff_map, ← charpolyRev_map, hM, charpolyRev_smul, Polynomial.comp_C_mul_X_coeff, smul_eq_C_mul,
    map_pow, mul_comm]

end Rev

theorem topCoeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun y => C c * X y) Q) = c ^ n * topCoeff Q := by
  unfold topCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hdeg : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ).sum (fun _ e => e) = n := by
    change Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n

    simp [map_sum]
  rw [coeff_aeval_C_mul_X, hdeg]
  ring

theorem kappa_div : kappa ^ n / (Complex.I / 2) ^ n = (((Real.pi ^ n)⁻¹ : ℝ) : ℂ) := by
  rw [← div_pow, Complex.ofReal_inv, Complex.ofReal_pow, ← inv_pow]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [kappa]
  field_simp

end GlobalTheory.ChernTopDens


open GlobalTheory.ChernTopDens in
theorem GlobalTheory.ChernCalc.dens_chernAt_re (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ)
    (v : V n) :
    (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re =
      chernTop R G v := by
  let Φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n := (aeval sym).comp (aeval fun y => C kappa * X y)
  have h1 : (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) =
      fun x => Φ (chernPoly (fun u => G u x.1) v x.2) := by
    funext x
    simp only [Φ, AlgHom.comp_apply, aeval_chernPoly, map_smul, chernAt]
  have h2 : aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) =
      aeval sym (aeval (fun y => C kappa * X y)
        (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)) := by
    rw [h1, ← comp_aeval, AlgHom.comp_apply, aeval_map_algebraMap]
    rfl
  rw [h2, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_aeval_C_mul_X, mul_div_right_comm, kappa_div, Complex.re_ofReal_mul]
  rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityChernPolynomialReEqChernPolyTopDensityStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.topDensity_chernPolynomial_re_eq_chernPolyTopDensity : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) (v : V n), (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re = chernTop R G v := by
  first | exact @GlobalTheory.ChernCalc.dens_chernAt_re | exact GlobalTheory.ChernCalc.dens_chernAt_re | (intros; apply GlobalTheory.ChernCalc.dens_chernAt_re <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPart

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

open GlobalTheory.ChartGlue

namespace GlobalTheory.ChernCalc

theorem chartMeas_congr_source {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {n : ℕ}
    (e : OpenPartialHomeomorph Y (V n)) {ρ ρ' : Y → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  unfold chartMeas
  congr 1
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => ?_)
  exact h _ (e.map_target hv)

theorem chernTopPart_eq_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  intro F _ σ X ι m E H R ε
  unfold chernTopPart HolAtlas.part glueMeas
  refine iSup_congr fun c => chartMeas_congr_source _ fun y hy => ?_
  have hx : (atlas X σ).loc (evalF (atlas X σ) (chernF E H) R) c (c.e y) =
      evalF (atlas X σ) (chernF E H) R ⟨(c, y), hy⟩ :=
    HolAtlas.loc_crd (atlas X σ) (evalF (atlas X σ) (chernF E H) R) ⟨(c, y), hy⟩
  show ENNReal.ofReal (_ * chernTop _ _ _) = ENNReal.ofReal (_ * (dens ((atlas X σ).loc _ c (c.e y))).re)
  rw [hx]
  congr 2
  exact (GlobalTheory.T.topDensity_chernPolynomial_re_eq_chernPolyTopDensity X.dim ι m R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)).symm

end GlobalTheory.ChernCalc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPartStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  first | exact @GlobalTheory.ChernCalc.chernTopPart_eq_part | exact GlobalTheory.ChernCalc.chernTopPart_eq_part | (intros; apply GlobalTheory.ChernCalc.chernTopPart_eq_part <;> assumption)
end
end
