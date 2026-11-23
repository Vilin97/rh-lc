module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFirstBlockGroupEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitian
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBound
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitianStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.height_power_summable_rational_hermitian : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  first | exact @GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | exact GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | (intros; apply GlobalTheory.CompanionTheory.HermSum.summable_height_rpow <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlock

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HtPull

open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_one)
open GlobalTheory.StdUnn.Model

def leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) : GL (Fin n) R :=
  ⟨bl hn a.1 0 0 1, bl hn (a⁻¹).1 0 0 1,
    by rw [blockMatrix_multiply]; simp [blockMatrix_one], by rw [blockMatrix_multiply]; simp [blockMatrix_one]⟩

theorem det_leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) :
    Matrix.GeneralLinearGroup.det (leviBl hn a) = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, leviBl, bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMatrix_zero {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero, Matrix.submatrix_zero, Pi.zero_apply]

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem isHt_blockPull : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  intro D n ρ p hn ι hc hblk H hH
  refine ⟨hH.1.comp hc, fun g => hH.2.1 _, ?_⟩
  intro q hq a ha g
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  rw [ha] at hm
  have hι := hblk q a.1 b 0 d hm
  rw [blockMatrix_zero] at hι
  have hqP : ι q ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hι
  have hA : blkA (mat (ι q)) = (leviBl hn a).1 := by
    rw [hι, blkA_blk4]
    rfl
  show H (ι (q * g)) = _ * H (ι g)
  rw [map_mul, hH.2.2 _ hqP (leviBl hn a) hA, det_leviBl]

end GlobalTheory.CompanionTheory.HtPull

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlockStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.height_pullback_first_block : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  first | exact @GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | exact GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | (intros; apply GlobalTheory.CompanionTheory.HtPull.isHt_blockPull <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomain

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermFD

theorem integrable_of_cover {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A] [MeasurableAdd A] [ContinuousAdd A] (L : AddSubgroup A) [Countable L]
    (μ : Measure A) [μ.IsAddLeftInvariant] (𝓖 : Set A) (hFD : IsAddFundamentalDomain L 𝓖 μ) (h1 : μ 𝓖 = 1)
    (f : A → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hS : Summable (fun ζ : L => f ζ.1))
    (K : Set A) (hK : ∀ x, ∃ γ ∈ L, γ + x ∈ K) (κ : ℝ) (hκ : 0 ≤ κ)
    (hb : ∀ ζ ∈ L, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) : Integrable f μ := by
  have hpt : ∀ z : A, ∑' ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hK z
    have h2 : ∀ ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤
        ENNReal.ofReal (κ * f ((Equiv.subRight (⟨γ, hγ⟩ : L) ζ).1)) := by
      intro ζ
      apply ENNReal.ofReal_le_ofReal
      have e : ζ.1 + z = (ζ.1 - γ) + (γ + z) := by simp [sub_eq_add_neg, add_assoc]
      rw [e]
      exact hb _ (L.sub_mem ζ.2 hγ) _ hz
    refine (ENNReal.tsum_le_tsum h2).trans ?_
    rw [(Equiv.subRight (⟨γ, hγ⟩ : L)).tsum_eq (fun ζ : L => ENNReal.ofReal (κ * f ζ.1)),
      ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun ζ => mul_nonneg hκ (hf0 _)) (hS.mul_left κ)]
  have hm : ∀ g : L, AEMeasurable (fun x : A => ENNReal.ofReal (f (g +ᵥ x))) (μ.restrict 𝓖) := fun g =>
    (ENNReal.measurable_ofReal.comp (hf.comp (continuous_const.add continuous_id)).measurable).aemeasurable
  have hI : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    rw [hFD.lintegral_eq_tsum'', ← lintegral_tsum hm]
    calc _ ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) ∂μ :=
          lintegral_mono fun x => hpt x
      _ = _ := by simp [h1]
  exact ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall hf0)).2 (hI.trans_lt ENNReal.ofReal_lt_top)⟩



theorem integrable_of_periodisation_bound : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  intro D ρ lz 𝓖 hC f hf hf0 hS K hK κ hκ hb
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := by
    haveI : SecondCountableTopology (ratHerm D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  exact integrable_of_cover (ratHerm D ρ) lz 𝓖 hFD h1 f hf hf0 hS K hK κ hκ hb

end GlobalTheory.CompanionTheory.HermFD
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomainStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integrable_of_summable_fundamental_domain : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  first | exact @GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | exact GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | (intros; apply GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerIntegrableWeylOrbit

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermConv

theorem integrable_height_rpow : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (H : G D n → ℝ≥0), IsHt H →
  (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Integrable (fun ζ : hermA D ρ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) m.lz := by
  intro D n ρ p hn M m H hH hC τ hτ
  have hτ0 : 0 ≤ τ := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg ρ) hτ)
  have hadj0 : ∀ k l : ℕ, GlobalTheory.MixModel.adj (0 : Mx D k l) = 0 := by
    intro k l
    show ((0 : Mx D k l).map (cA D)).transpose = 0
    ext i j
    simp
  have hadj1 : GlobalTheory.MixModel.adj (1 : Mx D ρ ρ) = 1 := by
    show ((1 : Mx D ρ ρ).map (cA D)).transpose = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hadjn1 : GlobalTheory.MixModel.adj (-1 : Mx D ρ ρ) = -1 := by
    show ((-1 : Mx D ρ ρ).map (cA D)).transpose = -1
    rw [Matrix.map_neg _ (fun a => map_neg (cA D) a), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_neg, Matrix.transpose_one]
  have hone : GlobalTheory.StdUnn.blk4 (1 : Mx D ρ ρ) 0 0 1 = 1 := by
    show (Matrix.fromBlocks (1 : Mx D ρ ρ) 0 0 1).submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm = 1
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hJ1 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0 * GlobalTheory.StdUnn.blk4 0 (-1) 1 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  have hJ2 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) (-1) 1 0 * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  let u : GL (Fin (ρ + ρ)) (AE D) := ⟨GlobalTheory.StdUnn.blk4 0 1 (-1) 0, GlobalTheory.StdUnn.blk4 0 (-1) 1 0, hJ1, hJ2⟩
  have hu : GlobalTheory.MixModel.adj (u : Mx D (ρ + ρ) (ρ + ρ)) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * (u : Mx D (ρ + ρ) (ρ + ρ)) =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    show GlobalTheory.MixModel.adj (GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 *
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = GlobalTheory.StdUnn.blk4 0 1 (-1) 0
    rw [GlobalTheory.CompanionTheory.JacobiMaps.adjoint_symplectic_block_product, hadj0, hadj1, hadjn1]
    simp only [zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, neg_neg, mul_neg, neg_mul, sub_self, neg_zero]
  obtain ⟨ι, hιc, hιm⟩ := GlobalTheory.T.exists_first_block_group_embedding D n ρ p hn
  have hH' := GlobalTheory.T.height_pullback_first_block D n ρ p hn ι hιc hιm H hH
  let w' : G D ρ := GlobalTheory.CompanionTheory.JacobiMaps.mkG u hu
  have hw' : GlobalTheory.StdUnn.mat w' = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := GlobalTheory.CompanionTheory.JacobiMaps.mat_mkG u hu
  let nb : hermA D ρ → G D ρ := fun z => GlobalTheory.CompanionTheory.JacobiMaps.nAt (z : Mx D ρ ρ) z.2
  have hnb : ∀ z : hermA D ρ, GlobalTheory.StdUnn.mat (nb z) = GlobalTheory.StdUnn.blk4 1 (z : Mx D ρ ρ) 0 1 :=
    fun z => GlobalTheory.CompanionTheory.JacobiMaps.mat_nAt _ _
  have hS := GlobalTheory.T.height_power_summable_rational_hermitian D ρ (fun h => H (ι h)) hH' w' nb hw' hnb τ hτ
  have hιw : ι w' = M.w := by
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm w' 0 1 (-1) 0 hw', M.w_mat]
  have hιn : ∀ z : hermA D ρ, ι (nb z) = M.nzx z 0 := by
    intro z
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm (nb z) 1 (z : Mx D ρ ρ) 0 1 (hnb z), M.nzx_mat, hadj0, GlobalTheory.CompanionTheory.PcB.blockMatrix_one, GlobalTheory.CompanionTheory.JacobiMaps.blockMatrix_zero]
  have hf_eq : ∀ z : hermA D ρ, (H (M.w * M.nzx z 0) : ℝ) ^ τ = (H (ι (w' * nb z)) : ℝ) ^ τ := by
    intro z
    rw [map_mul, hιw, hιn]
  have hSum : Summable (fun ζ : ratHerm D ρ => (H (M.w * M.nzx (ζ : hermA D ρ) 0) : ℝ) ^ τ) := by
    simpa only [hf_eq] using hS
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := ρ)
  have hNc : Continuous fun z : hermA D ρ => M.nzx z 0 := GlobalTheory.CompanionTheory.PcB.continuous_nz M
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC
    ((fun z => M.nzx z 0) '' K) (hK.image hNc)
  refine GlobalTheory.T.integrable_of_summable_fundamental_domain D ρ m.lz m.𝓖 m.hz (fun ζ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) ?_ ?_ hSum K hKc (κ ^ τ)
    (Real.rpow_nonneg (by linarith) τ) ?_
  · exact (NNReal.continuous_coe.comp (hH.1.comp (continuous_const.mul hNc))).rpow_const fun _ => Or.inr hτ0
  · exact fun z => Real.rpow_nonneg (NNReal.coe_nonneg _) τ
  · intro ζ _ z hz
    have h1 : M.nzx (ζ + z) 0 = M.nzx ζ 0 * M.nzx z 0 := by
      rw [GlobalTheory.CompanionTheory.PcB.nzx_mul, add_zero]
    have h2 := hκ (M.nzx z 0) ⟨z, hz, rfl⟩ (M.w * M.nzx ζ 0)
    show (H (M.w * M.nzx (ζ + z) 0) : ℝ) ^ τ ≤ κ ^ τ * (H (M.w * M.nzx ζ 0) : ℝ) ^ τ
    rw [h1, ← mul_assoc, ← Real.mul_rpow (by linarith) (NNReal.coe_nonneg _)]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) h2 hτ0

end GlobalTheory.CompanionTheory.HermConv

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerIntegrableWeylOrbitStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.height_power_integrable_weyl_orbit : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (H : G D n → ℝ≥0), IsHt H →
  (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Integrable (fun ζ : hermA D ρ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) m.lz := by
  first | exact @GlobalTheory.CompanionTheory.HermConv.integrable_height_rpow | exact GlobalTheory.CompanionTheory.HermConv.integrable_height_rpow | (intros; apply GlobalTheory.CompanionTheory.HermConv.integrable_height_rpow <;> assumption)
end
end
