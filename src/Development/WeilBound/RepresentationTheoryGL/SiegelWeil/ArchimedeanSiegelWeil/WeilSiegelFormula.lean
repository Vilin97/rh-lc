module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.HeadOfSiegel
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresentedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependentStatement
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalFormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCoefficientCongruencePullbackStatement
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilRankCoefficientStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariant

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem gramQ_mul_right (D : D7) (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    gramQ V (x * a) = (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * gramQ V x * a := by
  have hm : (x * a).map (D.sp.cm.sig : D.host.E → D.host.E) =
      x.map (D.sp.cm.sig : D.host.E → D.host.E) * a.map (D.sp.cm.sig : D.host.E → D.host.E) :=
    Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
  unfold gramQ
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def congrEquiv (D : D7) (V : HSp D) {r : ℕ} (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E)
    (ha : a.det ≠ 0) :
    {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = (congrH a β).1} :=
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hi : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have hi' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hu
  have hu' : IsUnit (a⁻¹).det := by
    have := congrArg Matrix.det hi
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at this)
  have hc : ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
      (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have hm : (a * a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) =
        a.map (D.sp.cm.sig : D.host.E → D.host.E) * (a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) :=
      Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [← hm, hi, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  { toFun := fun x => ⟨x.1 * a, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a x.1 hu]
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]; rfl⟩
    invFun := fun x => ⟨x.1 * a⁻¹, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a⁻¹ x.1 hu']
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]
      change ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
        ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a) * a⁻¹ = β.1
      calc _ = (((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
              (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ) * β.1 * (a * a⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = β.1 := by rw [hc, hi, Matrix.one_mul, Matrix.mul_one]⟩
    left_inv := fun x => Subtype.ext (by
      change x.1 * a * a⁻¹ = x.1
      rw [Matrix.mul_assoc, hi, Matrix.mul_one])
    right_inv := fun x => Subtype.ext (by
      change x.1 * a⁻¹ * a = x.1
      rw [Matrix.mul_assoc, hi', Matrix.mul_one]) }

theorem ifrB_congrH : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r)
    (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  intro D V ν r φ β a ha
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = (congrH a β).1},
        φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = β.1},
        pull a φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) := by
    funext h
    rw [← (congrEquiv D V β a ha).tsum_eq]
    refine tsum_congr fun x => ?_
    have hm : (x.1 * a).map (incA D) = HMul.hMul (x.1.map (incA D)) (a.map (incA D)) :=
      Matrix.map_mul (f := incA D)
    change φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((x.1 * a).map (incA D))) =
      φ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))) (a.map (incA D)))
    rw [hm, Matrix.mul_assoc]
  unfold IfrB
  rw [key]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariantStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_integral_congruence_invariant : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullback

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def rightMulEquiv {m r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    Matrix (Fin m) (Fin r) D.host.E ≃ Matrix (Fin m) (Fin r) D.host.E where
  toFun ξ := ξ * a
  invFun ξ := ξ * a⁻¹
  left_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv a hu]
  right_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul a hu]

theorem invPt_mul (V : HSp D) {r : ℕ} (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    GlobalTheory.SiegelFormula.invPt V h (ξ * a) =
      HMul.hMul (GlobalTheory.SiegelFormula.invPt V h ξ) (a.map (incA D)) := by
  unfold GlobalTheory.SiegelFormula.invPt
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem absTheta_pull (V : HSp D) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) (h : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V (pull a φ) h = GlobalTheory.SiegelFormula.absTheta V φ h := by
  unfold GlobalTheory.SiegelFormula.absTheta
  rw [← (rightMulEquiv (m := V.rank) a ha).tsum_eq
    (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)]
  refine tsum_congr fun ξ => ?_
  show ‖φ _‖ₑ = ‖φ (GlobalTheory.SiegelFormula.invPt V h (ξ * a))‖ₑ
  rw [invPt_mul]

theorem absThetaInt_pull (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    GlobalTheory.SiegelFormula.absThetaInt V ν (pull a φ) = GlobalTheory.SiegelFormula.absThetaInt V ν φ := by
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have : GlobalTheory.SiegelFormula.absTheta V (pull a φ) = GlobalTheory.SiegelFormula.absTheta V φ :=
    funext (absTheta_pull V φ a ha)
  rw [this]

theorem hyp_pull : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  intro D r V ψ θ μ lam ν φ a ha ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hli : LinearIndependent D.host.E a :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det a).mpr (isUnit_iff_ne_zero.mpr ha))
  refine ⟨h1, h2, h3, h4, h5, h6, GlobalTheory.T.pullback_schwartz_linear_independent D θ h3 _ _ _ a hli φ h7, ?_⟩
  rw [absThetaInt_pull V ν φ a ha]
  exact h8

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullbackStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hypotheses_preserved_by_linear_pullback : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelDeg

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem siegelDeg : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg := by
  intro D r V ψ θ μ lam ν φ hH β hβ
  obtain ⟨a, t, γ, ha, hγ, rfl⟩ := GlobalTheory.T.singular_hermitian_congruent_block_normal_form D r β hβ
  rw [GlobalTheory.T.frame_integral_congruence_invariant D V ν r φ γ a ha, ← GlobalTheory.T.whittaker_coefficient_congruence_pullback D r V ψ μ lam φ γ a ha hH.2.2.2.1 hH.2.2.2.2.1]
  have hH' := GlobalTheory.T.hypotheses_preserved_by_linear_pullback D r V ψ θ μ lam ν φ a ha hH
  by_cases hx : ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = γ.1
  · exact GlobalTheory.T.siegel_weil_rank_coefficient D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx
  · exact GlobalTheory.T.frame_integral_eq_coefficient_nonrepresented D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.WeilSiegelFormula

section

@[expose] public section

theorem PositivityTheory.Rg.Wsf.weilSiegelFormula : GlobalTheory.Published.WeilSiegelFormula :=
  PositivityTheory.PfWsf.Top.head_of_deg GlobalTheory.CompanionTheory.WeilSiegel.Deg.siegelDeg
end
end
