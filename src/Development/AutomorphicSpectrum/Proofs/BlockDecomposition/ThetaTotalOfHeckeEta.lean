module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTotalOfEuclideanStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMajorantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProductsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFiniteStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.LeftInvSect
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem iwaCpt : IwaCpt := by
  intro D n C hC
  have hCK : IsCompact (C * (K D n : Set (G D n))⁻¹) := hC.mul isCompact_K.inv
  have hQ : IsCompact ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) :=
    (isClosed_P (D := D) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hCK
  have hL := hQ.image (continuous_leviBlock (D := D) (n := n))
  set L := leviBlock (D := D) (n := n) '' ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) with hLdef
  have hR : Continuous fun a : GL (Fin n) (AE D) => (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_absE.comp continuous_detGL)
  obtain ⟨R, hRb⟩ := (hL.image hR).bddAbove
  refine ⟨Units.val '' L, (fun a : GL (Fin n) (AE D) => (a⁻¹).1) '' L, R, hL.image Units.continuous_val,
    hL.image Units.continuous_coe_inv, fun h hh => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := Iwasawa.exists_mul D n h
  have hmem : leviBlock (D := D) (n := n) ⟨q, hq⟩ ∈ L :=
    ⟨⟨q, hq⟩, ⟨q * k, hh, k⁻¹, Set.inv_mem_inv.2 hk, by simp⟩, rfl⟩
  obtain ⟨m, t, b, e, hm, ht⟩ := exists_levi_unip hq (leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  exact ⟨m, t, k, _, b, hk, by rw [e], hm, ht, ⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩, hRb ⟨_, hmem, rfl⟩⟩

end GlobalTheory.CompanionTheory.ThTot

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactnessStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt | exact GlobalTheory.CompanionTheory.ThTot.iwaCpt | (intros; apply GlobalTheory.CompanionTheory.ThTot.iwaCpt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatementStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.product_measure_statement : ProdMeas := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | exact GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensorStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.product_theta_of_schwartz_tensor : SchwTensor → ProdTh := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | exact GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotalStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.rank_one_theta_total : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | exact GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensityStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.schwartz_tensor_density : SchwTensor := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | exact GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotalStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.zero_coefficient_total : ZeroTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.zeroTotal | exact GlobalTheory.CompanionTheory.ThTot.zeroTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.zeroTotal <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsIsCovolOneRatMx

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi Formalism.IndefR.Mult MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatMxCovol

theorem exists_isCovolOne_ratMx : ∀ (D : D7) (m n : ℕ), ∃ (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 := by
  intro D m n
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  exact GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (Mx D m n) (ratMx D m n) ⟨i5, K, hK, hc⟩

end GlobalTheory.CompanionTheory.RatMxCovol
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7}

def subH {k m : ℕ} (b : HermE D m) (e : Fin k → Fin m) : HermE D k :=
  ⟨b.1.submatrix e e, by
    have h := b.2
    funext i j
    exact congrFun (congrFun h (e i)) (e j)⟩

theorem subH_isDiagInv {k m : ℕ} {b : HermE D m} (hb : IsDiagInv b) {e : Fin k → Fin m} (he : Function.Injective e) :
    IsDiagInv (subH b e) := by
  obtain ⟨h1, h2⟩ := hb
  have hd : ∀ i, b.1 i i ≠ 0 := by
    intro i h0
    apply h2
    rw [← h1.diagonal_diag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hs : (subH b e).1.IsDiag := h1.submatrix he
  refine ⟨hs, ?_⟩
  rw [← hs.diagonal_diag, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hd (e i)

theorem diagonal_invertible_block_form {ρ : ℕ} {b : HermE D (ρ + 1)} (hb : IsDiagInv b) :
    IsBlockSL2Embedding b (subH b (Fin.castAdd 1)) (subH b (Fin.natAdd ρ)) := by
  have hne : ∀ (i : Fin ρ) (j : Fin 1), Fin.castAdd 1 i ≠ Fin.natAdd ρ j := by
    intro i j h
    have := congrArg Fin.val h
    simp at this
    omega
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun i j => hb.1 (hne i j), fun i j => hb.1 (hne i j).symm⟩

theorem core (h0 : ZeroTotal) (h1 : OneTotal) (hS : StepTotal) (hH : HeckeEta) (D : D7) :
    ∀ (ρ p : ℕ) (μ : Measure (Mx D ρ p)) (𝓕 : Set (Mx D ρ p)), IsCovolOne (ratMx D ρ p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, IsDiagInv b₀ → ∀ χ, IsHeckeChar D χ → ResEta D χ ρ → (ρ = 0 → χ = 1) →
    ∀ θ, IsInfFam θ → Total ψ χ θ b₀ μ := by
  intro ρ
  induction ρ with
  | zero =>
    intro p μ 𝓕 hμ ψ hψ b₀ _ χ _ _ h1' θ hθ
    obtain rfl := h1' rfl
    exact h0 D p μ 𝓕 hμ ψ hψ b₀ θ hθ
  | succ ρ ih =>
    intro p μ 𝓕 hμ ψ hψ b₀ hb χ hχ hr _ θ hθ
    obtain ⟨χ₁, hχ₁, hr₁, he⟩ : ∃ χ₁, IsHeckeChar D χ₁ ∧ ResEta D χ₁ 1 ∧ (ρ = 0 → χ₁ = χ) := by
      by_cases h : ρ = 0
      · subst h
        exact ⟨χ, hχ, hr, fun _ => rfl⟩
      · obtain ⟨χ₁, a, b⟩ := hH D 1
        exact ⟨χ₁, a, b, fun h' => absurd h' h⟩
    have hχ' : IsHeckeChar D (χ * χ₁⁻¹) := by
      refine ⟨?_, fun x => ?_⟩
      · have c1 := hχ.1
        have c2 := hχ₁.1
        exact c1.mul c2.inv
      · have a1 := hχ.2 x
        have a2 := hχ₁.2 x
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, a1, a2, inv_one, mul_one]
    have hr' : ResEta D (χ * χ₁⁻¹) ρ := by
      refine ⟨hr.1, fun η hη a => ?_⟩
      have e1 := hr.2 η hη a
      have e2 := hr₁.2 η hη a
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1, e2, pow_one, pow_succ]
      exact mul_inv_cancel_right _ _
    obtain ⟨μr, 𝓕r, hμr⟩ := GlobalTheory.CompanionTheory.RatMxCovol.exists_isCovolOne_ratMx D ρ p
    obtain ⟨μs, 𝓕s, hμs⟩ := GlobalTheory.CompanionTheory.RatMxCovol.exists_isCovolOne_ratMx D 1 p
    have hinj1 : Function.Injective (Fin.castAdd 1 : Fin ρ → Fin (ρ + 1)) := Fin.castAdd_injective _ _
    have hinj2 : Function.Injective (Fin.natAdd ρ : Fin 1 → Fin (ρ + 1)) := Fin.natAdd_injective _ _
    have hd2 := subH_isDiagInv hb hinj2
    have T := hS D ρ 1 p μr 𝓕r μs 𝓕s μ 𝓕 hμr hμs hμ ψ hψ (χ * χ₁⁻¹) χ₁ θ hθ _ _ b₀ (diagonal_invertible_block_form hb)
      (ih p μr 𝓕r hμr ψ hψ _ (subH_isDiagInv hb hinj1) _ hχ' hr'
        (fun h => by rw [he h]; exact mul_inv_cancel χ) θ hθ)
      (h1 D p μs 𝓕s hμs ψ hψ _ hd2.2 χ₁ hχ₁ hr₁ θ hθ)
    rwa [inv_mul_cancel_right] at T

theorem thTotal_of (h0 : ZeroTotal) (h1 : OneTotal) (hS : StepTotal) : HeckeEta → ThTotal := by
  intro hH D ρ p m ψ hψ b₀ hb χ hχ hr h0' θ hθ
  exact core h0 h1 hS hH D ρ p m.μ m.𝓕 m.hμ ψ hψ b₀ hb χ hχ hr h0' θ hθ

theorem thTotal : HeckeEta → ThTotal :=
  thTotal_of GlobalTheory.T.zero_coefficient_total
    (GlobalTheory.T.rank_one_theta_total GlobalTheory.T.weil_representation_continuity (GlobalTheory.T.rank_one_majorant GlobalTheory.T.weil_representation_continuity GlobalTheory.T.weil_representation_K_finite GlobalTheory.T.orbit_majorant GlobalTheory.T.iwasawa_compactness)
      (GlobalTheory.T.fock_total_of_euclidean GlobalTheory.T.euclidean_total))
    (GlobalTheory.T.step_total_of_products (GlobalTheory.T.product_theta_of_schwartz_tensor GlobalTheory.T.schwartz_tensor_density) GlobalTheory.T.product_measure_statement)

end GlobalTheory.CompanionTheory.ThTot

end
end
end
