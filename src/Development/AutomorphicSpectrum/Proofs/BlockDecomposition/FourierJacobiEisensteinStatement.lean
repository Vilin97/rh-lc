module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableMatricesAndCosetsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiExpansionBoundedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiTermsSummableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTransformInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreservedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTwistedSumPeriodicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedAltBis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolic
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSumStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterProperties
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientHeisenbergEquivarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLatticeSumsBoundedProductStatement
import Mathlib.Topology.UniformSpace.Uniformizable

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolicStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.section_left_invariant_rational_parabolic : ∀ {D : D7} {n : ℕ} (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsHeckeChar D χ → IsLaw χ s f → LeftInv (P D n ⊓ GF D n) f := by
  first | exact @GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | exact GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | (intros; apply GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableCoefficientComposition

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE




theorem Wz_stronglyMeasurable : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (f : G D n → ℂ), Continuous f → ∀ {X : Type} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (c : X → G D n), Continuous c → StronglyMeasurable fun v => Wz M m ψ b₀ f (c v) := by
  intro D n ρ p hn M m ψ hψ b₀ f hf X _ _ _ _ c hc
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D ρ) :=
    (GlobalTheory.CompanionTheory.FourierN.isClosed_hermA (D := D) (n := ρ)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := m.hz.1
  haveI : SFinite m.lz := inferInstance
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hcont : Continuous fun u : X × hermA D ρ => f (M.w * M.nzx u.2 0 * c u.1) * conj (chz ψ b₀ u.2) := by
    refine (hf.comp ((continuous_const.mul ?_).mul (hc.comp continuous_fst))).mul (hchz.comp continuous_snd)
    exact M.nzx_cont.comp (continuous_snd.prodMk continuous_const)
  exact hcont.stronglyMeasurable.integral_prod_right

end GlobalTheory.CompanionTheory.FJE
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableCoefficientCompositionStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stronglyMeasurable_coefficient_composition : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (f : G D n → ℂ), Continuous f → ∀ {X : Type} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (c : X → G D n), Continuous c → StronglyMeasurable fun v => Wz M m ψ b₀ f (c v) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable | exact GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable | (intros; apply GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwap

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem term_after : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ hTw χ' hχ' θ hθ Ω hΩ χ s f hf g γ hγ T hT v
  obtain ⟨z', hz'⟩ := hT v.1 v.2
  have hz : M.emb γ * (M.nzx 0 v.2 * M.sh v.1) = M.nzx z' (T v).2 * M.sh (T v).1 * M.emb γ := hz'
  have hterm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      Wz M m ψ b₀ f (M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))) =
        chz ψ b₀ z' * (chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) := by
    intro η
    have e1 : M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)) =
        M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
      calc M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))
          = M.sh (rt η) * ((M.emb γ * (M.nzx 0 v.2 * M.sh v.1)) * g) := by simp only [mul_assoc]
        _ = M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
            rw [hz]; simp only [mul_assoc]
    have e2 : M.sh (rt η) * (M.sh (T v).1 * M.emb γ * g) = M.sh (rt η + (T v).1) * M.emb γ * g := by
      rw [← sh_add M (rt η) (T v).1]; simp only [mul_assoc]
    rw [e1, GlobalTheory.T.coefficient_heisenberg_equivariance M m ψ hψ b₀ χ s f hf (rt η) z' (T v).2 _, e2, mul_assoc]
  obtain ⟨-, hnorm, -, -⟩ := GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀
  have hchv : ∀ x y : Mx D ρ p, ‖chv ψ b₀ x y‖ = 1 := fun x y => hψ.2.1 _
  have hth : th ψ b₀ (Ω 1) 0 v.2 v.1 = chz ψ b₀ z' * dsum ψ b₀ (Ω γ) (T v).2 (T v).1 := by
    rw [hTw D n ρ p hn M m ψ hψ b₀ hb₀ χ' hχ' θ hθ Ω hΩ γ hγ 0 v.2 v.1 z' (T v).2 (T v).1 hz]
    rfl
  have hcc : chz ψ b₀ z' * conj (chz ψ b₀ z') = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  refine ⟨fun η => ?_, ?_⟩
  · rw [hterm η, norm_mul, norm_mul, hnorm, hchv, one_mul, one_mul]
  · simp_rw [hterm]
    rw [tsum_mul_left, hth, map_mul, Ap]
    have hd : (∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
        chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) =
        dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 := rfl
    rw [hd]
    calc _ = (chz ψ b₀ z' * conj (chz ψ b₀ z')) *
          (dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 *
            conj (dsum ψ b₀ (Ω γ) (T v).2 (T v).1)) := by ring
      _ = _ := by rw [hcc, one_mul]

end GlobalTheory.CompanionTheory.FJE
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwapStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_fourier_jacobi_lattice_swap : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.term_after | exact GlobalTheory.CompanionTheory.FJE.term_after | (intros; apply GlobalTheory.CompanionTheory.FJE.term_after <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CompanionTheory.FJE in
theorem GlobalTheory.CompanionTheory.FJE.fjEis : ZUnfold → ThTwist → FJEis := by
  intro hZ hTw D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ s f hf hl hs g
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : m.μ.IsAddHaarMeasure := m.hμ.1
  obtain ⟨hcM, hcC⟩ := GlobalTheory.T.countable_matrices_and_cosets D ρ p
  have hsum := fun g' => (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g').1
  have hC := (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g).2
  obtain ⟨t, ht, hT⟩ := GlobalTheory.T.fourier_jacobi_terms_summable M m ψ hψ b₀ χ s f hl g hC
  have hF : LeftInv (GF D n) (eisS f) := GlobalTheory.Eis.leftInv_cosetSum (GlobalTheory.T.section_left_invariant_rational_parabolic χ s f hχ hl)
  have hTr := fun q : GlobalTheory.Eis.Cosets (P D p) (GF D p) => GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) q.out.2
  choose T hT1 hT2 hT3 using hTr

  have hterm := fun (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (v : Mx D ρ p × Mx D ρ p) =>
    GlobalTheory.T.theta_fourier_jacobi_lattice_swap M m ψ hψ b₀ hb hTw χ' hχ' θ hθ Ω hΩ χ s f hl g ((q.out : GF D p) : G D p) q.out.2 (T q) (hT3 q) v

  set A : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Matrix (Fin ρ) (Fin p) D.host.E → Mx D ρ p × Mx D ρ p → ℂ :=
    fun q η v => Wz M m ψ b₀ f (M.sh (rt η) * M.emb (q.out : GF D p) * (M.nzx 0 v.2 * (M.sh v.1 * g))) with hA
  set Sq : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Mx D ρ p × Mx D ρ p → ℂ := fun q v => ∑' η, A q η v with hSq
  have hAs : ∀ q v, Summable (fun η => ‖A q η v‖) := fun q v =>
    (summable_congr fun η => (hterm q v).1 η).2 (hT q (T q v).1).1
  have hSqle : ∀ q v, ‖Sq q v‖ ≤ t q := fun q v => by
    refine (norm_tsum_le_tsum_norm (hAs q v)).trans ?_
    rw [tsum_congr fun η => (hterm q v).1 η]
    exact (hT q (T q v).1).2
  have hAm : ∀ q η, StronglyMeasurable (A q η) := fun q η =>
    GlobalTheory.T.stronglyMeasurable_coefficient_composition M m ψ hψ b₀ f hf _ (by
      have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
        M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
      have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
      exact continuous_const.mul (h1.mul (h2.mul continuous_const)))
  have hSqm : ∀ q, StronglyMeasurable (Sq q) := fun q =>
    GlobalTheory.CompanionTheory.FJE.tsum_meas (fun η => hAm q η) fun v => (hAs q v).of_norm
  set Fz : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ (eisS f) (M.nzx 0 v.2 * (M.sh v.1 * g)) with hFz
  have hq : ∀ v, HasSum (fun q => Sq q v) (Fz v) := fun v =>
    (hsum (M.nzx 0 v.2 * (M.sh v.1 * g))).prod_fiberwise fun q => (hAs q v).of_norm.hasSum
  have hqn : ∀ v, Summable fun q => ‖Sq q v‖ := fun v => .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hSqle q v) ht
  have hFzm : StronglyMeasurable Fz := by
    have : Fz = fun v => ∑' q, Sq q v := funext fun v => (hq v).tsum_eq.symm
    rw [this]
    exact GlobalTheory.CompanionTheory.FJE.tsum_meas hSqm fun v => (hqn v).of_norm
  have hFzb : ∀ y x, ‖zc M m ψ b₀ (eisS f) (M.nzx 0 x * (M.sh y * g))‖ ≤ ∑' q, t q := fun y x => by
    have := (hq (y, x)).tsum_eq
    simp only [hFz] at this
    rw [← this]
    exact (norm_tsum_le_tsum_norm (hqn _)).trans ((hqn _).tsum_le_tsum (fun q => hSqle q _) ht)
  have h1 := GlobalTheory.T.fourier_jacobi_expansion_bounded M m ψ hψ b₀ (eisS f) hF g θ hθ (Ω 1) (hΩ.mem 1) _ hFzb hFzm

  have hcont : ∀ h, Continuous (Ω h) := fun h => hΩ.cont.comp (continuous_const.prodMk continuous_id)
  have hsm : ∀ h, StronglyMeasurable (Ω h) := fun h => (hcont h).stronglyMeasurable
  have hbd := fun h => GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA θ hθ (Ω h) (hΩ.mem h)
  obtain ⟨Bθ, hBθ⟩ := hbd 1
  have hthm : StronglyMeasurable fun v : Mx D ρ p × Mx D ρ p => conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := by
    simp only [th_zero]
    exact Complex.continuous_conj.comp_stronglyMeasurable
      (GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum ψ hψ b₀ (Ω 1) (hsm 1) fun y => (hBθ y).1)
  have hthb : ∀ v : Mx D ρ p × Mx D ρ p, ‖conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ Bθ := fun v => by
    rw [RCLike.norm_conj, th_zero]
    have hn1 : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖chv ψ b₀ v.2 (rt ξ) * Ω 1 (rt ξ + v.1)‖ = ‖Ω 1 (rt ξ + v.1)‖ := fun ξ => by
      rw [norm_mul, (GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀).2.2.1, one_mul]
    refine (norm_tsum_le_tsum_norm ((summable_congr hn1).2 (hBθ v.1).1)).trans ?_
    rw [tsum_congr hn1]
    exact (hBθ v.1).2

  have hI : ∀ q, ∫ v in m.𝓕 ×ˢ m.𝓕, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) ∂(m.μ.prod m.μ) =
      Rsec M m ψ b₀ f g Ω (((q.out : GF D p) : G D p) * 1) := fun q => by
    have hΦm : StronglyMeasurable fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g) :=
      GlobalTheory.T.stronglyMeasurable_coefficient_composition M m ψ hψ b₀ f hf _ ((M.sh_cont.mul continuous_const).mul continuous_const)
    obtain ⟨B₂, hB₂⟩ := hbd ((q.out : GF D p) : G D p)
    have e1 : ∀ v, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) =
        Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g)) (Ω ((q.out : GF D p) : G D p)) (T q v) :=
      fun v => (hterm q v).2
    simp only [e1]
    rw [GlobalTheory.T.lattice_transform_invariance m (T q) (hT1 q) (hT2 q) _ (fun ξ₁ ξ₂ v => GlobalTheory.T.lattice_twisted_sum_periodic ψ hψ b₀ _ _ ξ₁ ξ₂ v),
      GlobalTheory.T.twisted_lattice_sums_bounded_product m ψ hψ b₀ hb _ _ (t q) B₂ hΦm (hsm _) (fun y => hT q y) hB₂, mul_one]
    rfl

  set ν := (m.μ.prod m.μ).restrict (m.𝓕 ×ˢ m.𝓕) with hν
  have hmass : ν Set.univ = 1 := by
    rw [hν, Measure.restrict_apply_univ, Measure.prod_prod, m.hμ.2.2, one_mul]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hbound : ∀ q v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ t q * Bθ := fun q v => by
    rw [norm_mul]
    exact mul_le_mul (hSqle q v) (hthb v) (norm_nonneg _) ((norm_nonneg _).trans (hSqle q v))
  have hint : ∀ q, Integrable (fun v => Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) ν := fun q =>
    Integrable.of_bound ((hSqm q).mul hthm).aestronglyMeasurable (t q * Bθ) (.of_forall (hbound q))
  have hnorm : ∀ q, ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν ≤ t q * Bθ := fun q => by
    have h2 := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun v => ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖) (C := t q * Bθ)
      (.of_forall fun v => by simpa using hbound q v)
    have h3 : ν.real Set.univ = 1 := by simp [Measure.real, hmass]
    rw [h3, mul_one] at h2
    exact (le_abs_self _).trans (by simpa using h2)
  have hfs : Summable fun q => ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν :=
    .of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm (ht.mul_right Bθ)
  have hfin2 := hasSum_integral_of_summable_integral_norm hint hfs
  have e : (fun v => ∑' q, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) =
      fun v => Fz v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := funext fun v => by
    rw [tsum_mul_right, (hq v).tsum_eq]
  rw [e] at hfin2
  rw [h1, ← hfin2.tsum_eq, eisS, GlobalTheory.Eis.cosetSum]
  exact tsum_congr fun q => hI q
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisensteinStatement

section

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.fourier_jacobi_eisenstein : ZUnfold → ThTwist → FJEis := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fjEis | exact GlobalTheory.CompanionTheory.FJE.fjEis | (intros; apply GlobalTheory.CompanionTheory.FJE.fjEis <;> assumption)
end
end
