module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneColumnJoinProductStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumPartialFourierUnfoldingStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBounded
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilActionBlockMatrixComponentsStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfoldingStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.block_weil_action_theta_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E), (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b →
    ∀ (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s))),
    xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a) →
    yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) →
    ∀ (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E),
      Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | exact GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Summand.summand <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfoldingStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eisenstein_coefficient_block_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | exact GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfolding

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.NegStep

theorem integral_neg_of_secondCountable {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → E) :
    ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  have : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  exact integral_neg_eq_self f μ

theorem colJoin_zero_mul {R : Type*} [NonUnitalNonAssocSemiring R] {m r s : ℕ} (p : Matrix (Fin m) (Fin r) R)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) R) (c : Matrix (Fin r) (Fin (r + s)) R)
    (h : ∀ j : Fin r, a (Fin.castAdd s j) = c j) :
    colJoin p (0 : Matrix (Fin m) (Fin s) R) * a = p * c := by
  ext i k
  simp [Matrix.mul_apply, Fin.sum_univ_add, h]

theorem inner_neg_neg {D : D7} (V : HSp D) {n : ℕ} (t : Mx D V.rank n) : inner V (-t) (-t) = inner V t t := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem integral_colJoin_neg_eq_J : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  intro D ψ V r s μr 𝓕r hcov c a hca b Φ
  obtain ⟨h1, h2, h3, h4, -⟩ := lattice_Mx D V.rank r
  have hB : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hH : μr.IsAddHaarMeasure := hcov.1
  have hrow : ∀ j : Fin r, rat a (Fin.castAdd s j) = rat c j := by
    intro j
    have := hca.2 (Fin.castAdd s j) j.isLt
    funext k
    show incA D (a (Fin.castAdd s j) k) = incA D (c j k)
    rw [this]
    rfl
  have key : ∀ t : Mx D V.rank r,
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) =
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))) (-t) := by
    intro t
    have e : (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a) : Mx D V.rank (r + s)) = HMul.hMul (-t) (rat c) :=
      colJoin_zero_mul (-t) (rat a) (rat c) hrow
    show _ = Φ (HMul.hMul (-t) (rat c)) * _
    rw [e, inner_neg_neg, mul_comm]
  exact (integral_congr_ae (Filter.Eventually.of_forall key)).trans
    (integral_neg_of_secondCountable (E := ℂ) μr
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))))

end GlobalTheory.CompanionTheory.EisUnfold.NegStep
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfoldingStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eisenstein_hermitian_integral_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | exact GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.schwartz_lattice_sum_bounded : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n →
    Continuous φ ∧ ∃ B : ℝ≥0, ∀ w : Mx D m n, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖φ (rat ξ + w)‖ₑ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | exact GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTerm

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

theorem unfold2 : Unfold2 := by
  intro D ψ hψ θ hθ V n r hrn μ 𝓕 hμ μr h𝓕r c a hca b Φ hΦ
  obtain ⟨𝓕r, hμr⟩ := h𝓕r
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain ⟨μs, 𝓕s, hμs⟩ := exists_isCovolOne D V.rank s
  obtain ⟨hΦc, B, hB⟩ := GlobalTheory.T.schwartz_lattice_sum_bounded D θ hθ V.rank (r + s) Φ hΦ
  have ha : IsUnit a.det := hca.1

  let e : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E ≃
      Matrix (Fin V.rank) (Fin (r + s)) D.host.E :=
    joinEquiv.trans
      { toFun := fun ξ => ξ * a
        invFun := fun ξ => ξ * a⁻¹
        left_inv := fun ξ => Matrix.mul_nonsing_inv_cancel_right a ξ ha
        right_inv := fun ξ => Matrix.nonsing_inv_mul_cancel_right a ξ ha }
  set T : Mx D V.rank (r + s) → ℂ := fun y => ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E,
    Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
      (ξ.map (incA D)) with hT
  have hform : ∀ y₁ y₂, T (colJoin y₁ y₂) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 y₁ y₂ := by
    intro y₁ y₂
    obtain ⟨hx, hy⟩ := GlobalTheory.T.weil_action_block_matrix_components D V.rank r s b.1 a y₁ y₂
    rw [hT]
    dsimp only
    rw [← e.tsum_eq]
    exact tsum_congr fun pq => GlobalTheory.T.block_weil_action_theta_unfolding D ψ hψ V r s b.1 b.2 a ha Φ y₁ y₂ _ hx hy pq.1 pq.2
  have hper : ∀ γ ∈ ratMx D V.rank (r + s), ∀ y, T (γ + y) = T y := by
    intro γ hγ y
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [← colJoin_colL_colR g, ← colJoin_colL_colR y, rat_colJoin, ← colJoin_add, hform, hform,
      add_comm (rat (colL g)), add_comm (rat (colR g))]
    exact GlobalTheory.T.lattice_sum_shift_invariant D ψ hψ V r s b.1 a Φ (colL g) (colR g) (colL y) (colR y)
  have hE := GlobalTheory.T.covolume_one_column_join_product D V.rank r s μr 𝓕r μs 𝓕s hμr hμs
  show ∫ y in 𝓕, T y ∂μ = _
  rw [covolOne_integral_eq hE hμ T hper]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D V.rank s
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D V.rank (r + s)
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank (r + s)) := ⟨rfl⟩
  have hc : Continuous fun z : Mx D V.rank r × Mx D V.rank s => colJoin z.1 z.2 := by
    refine continuous_matrix fun i k => ?_
    simp only [colJoin, Matrix.of_apply]
    rcases finSumFinEquiv.symm k with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd
  have hc' : Continuous fun y : Mx D V.rank (r + s) => ((colL y, colR y) : Mx D V.rank r × Mx D V.rank s) := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_)
    · exact continuous_apply_apply i (Fin.castAdd s j)
    · exact continuous_apply_apply i (Fin.natAdd r j)
  let hj : (Mx D V.rank r × Mx D V.rank s) ≃ₜ Mx D V.rank (r + s) :=
    { (joinEquiv : (Mx D V.rank r × Mx D V.rank s) ≃ Mx D V.rank (r + s)) with
      continuous_toFun := hc
      continuous_invFun := hc' }
  have hmp : MeasurePreserving hj.toMeasurableEquiv (μr.prod μs)
      ((μr.prod μs).map fun z => colJoin z.1 z.2) := ⟨hj.toMeasurableEquiv.measurable, rfl⟩
  have h1 := hmp.setIntegral_image_emb hj.toMeasurableEquiv.measurableEmbedding T (𝓕r ×ˢ 𝓕s)
  erw [h1]
  have h2 : ∀ z : Mx D V.rank r × Mx D V.rank s, T (hj.toMeasurableEquiv z) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 z.1 z.2 := fun z => hform z.1 z.2
  simp only [h2]
  rw [GlobalTheory.T.eisenstein_coefficient_block_unfolding D ψ hψ V r s μr 𝓕r μs 𝓕s hμr hμs b.1 a ha Φ hΦc B hB]
  exact GlobalTheory.T.eisenstein_hermitian_integral_unfolding D ψ V r s μr 𝓕r hμr c a hca b Φ

end GlobalTheory.CompanionTheory.EisUnfold

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTermStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_unfolding_second_term : PositivityTheory.GramSchwartzFunctions.EC.Unfold2 := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.unfold2 | exact GlobalTheory.CompanionTheory.EisUnfold.unfold2 | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.unfold2 <;> assumption)
end
end
