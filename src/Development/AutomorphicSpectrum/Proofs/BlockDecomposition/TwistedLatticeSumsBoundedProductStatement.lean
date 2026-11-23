module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSum
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterIntegralVanishes

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

variable {D : D7} {ρ p : ℕ}

open scoped Pointwise

theorem trace_single_mul_eq {R : Type} [CommRing R] {a b : ℕ} (j : Fin a) (i : Fin b) (w : R)
    (M : Matrix (Fin b) (Fin a) R) : Matrix.trace (Matrix.single j i w * M) = w * M i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem trA_algebraMap_half [Nontrivial (AF D.host.F)] (t : AF D.host.F) :
    trA (D := D) (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  show Algebra.trace (AF D.host.F) (AE D) (algebraMap (AF D.host.F) (AE D)
    (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t
  rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h2, two_nsmul, ← add_mul, ← map_add (f := _)]
  norm_num

theorem exists_chv_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (hdet : b₀.1.det ≠ 0) (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∃ x₀ : Mx D ρ p, chv ψ b₀ x₀ (rt ζ) ≠ 1 := by
  obtain ⟨-, -, -, t, ht⟩ := hψ
  have hB : b₀.1 * ζ ≠ 0 := by
    intro h0
    apply hζ
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hdet
    calc ζ = b₀.1⁻¹ * (b₀.1 * ζ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (b₀.1 * ζ) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB (Matrix.ext hc)
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = algebraMap (AF D.host.F) (AE D)
      (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) * incA D ((b₀.1 * ζ) i j)⁻¹ := ⟨_, rfl⟩
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have key : Matrix.trace (pr b₀ (adj (Matrix.single j i c)) (rt ζ)) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) := by
    show Matrix.trace (adj (adj (Matrix.single j i c)) * (b₀.1.map (incA D) * rt ζ)) = _
    rw [adj_adj, show b₀.1.map (incA D) * rt ζ = rat (b₀.1 * ζ) from (rat_mul _ _).symm,
      trace_single_mul_eq]
    show c * incA D ((b₀.1 * ζ) i j) = _
    rw [hc, mul_assoc, ← map_mul, inv_mul_cancel₀ hij, map_one, mul_one]
  show ψ (trA (Matrix.trace (pr b₀ _ (rt ζ)))) ≠ 1
  haveI : Nontrivial (AF D.host.F) :=
    nontrivial_of_ne t 0 (fun h => ht (by rw [h, AddChar.map_zero_eq_one]))
  rw [key, trA_algebraMap_half]
  exact ht

theorem integral_chv_rt_eq_zero {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (hdet : b₀.1.det ≠ 0)
    (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_chv_ne_one ψ hψ b₀ hdet ζ hζ
  obtain ⟨hadd, -, -, -, hrat, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀
  have hper : ∀ γ ∈ ratMx D ρ p, ∀ a, chv ψ b₀ (γ + a) (rt ζ) = chv ψ b₀ a (rt ζ) := by
    intro γ hγ a
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [hadd, show rat g = rt g from rfl, hrat, one_mul]
  have h := covolOne_integral_add m.hμ (fun x => chv ψ b₀ x (rt ζ)) hper x₀
  simp only [hadd] at h
  rw [MeasureTheory.integral_mul_const] at h
  have h2 : (∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ) * (chv ψ b₀ x₀ (rt ζ) - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hx₀)

end GlobalTheory.CompanionTheory.FJE
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterIntegralVanishesStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenberg_character_integral_vanishes : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ ζ : Matrix (Fin ρ) (Fin p) D.host.E, ζ ≠ 0 → ∫ x in m.𝓕, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ζ) ∂m.μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FJE.integral_chv_rt_eq_zero | exact GlobalTheory.CompanionTheory.FJE.integral_chv_rt_eq_zero | (intros; apply GlobalTheory.CompanionTheory.FJE.integral_chv_rt_eq_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterOrthogonality

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

theorem integral_mul_tsum_unimod {ι X : Type} [Countable ι] [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {c : ι → X → ℂ} {h : X → ℂ} {a : ι → ℂ} (hc : ∀ i, AEStronglyMeasurable (c i) ν)
    (hc1 : ∀ i x, ‖c i x‖ = 1) (hh : AEStronglyMeasurable h ν) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
    (ha : Summable fun i => ‖a i‖) :
    ∫ x, h x * ∑' i, c i x * a i ∂ν = ∑' i, (∫ x, h x * c i x ∂ν) * a i := by
  have hbd : ∀ i x, ‖h x * (c i x * a i)‖ ≤ B * ‖a i‖ := fun i x => by
    rw [norm_mul, norm_mul, hc1, one_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hint : ∀ i, Integrable (fun x => h x * (c i x * a i)) ν := fun i =>
    Integrable.of_bound (hh.mul ((hc i).mul aestronglyMeasurable_const)) (B * ‖a i‖)
      (Eventually.of_forall (hbd i))
  have hsum : Summable fun i => ∫ x, ‖h x * (c i x * a i)‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) (fun i => ?_)
      ((ha.mul_left B).mul_left (ν.real Set.univ))
    calc ∫ x, ‖h x * (c i x * a i)‖ ∂ν ≤ ∫ _, B * ‖a i‖ ∂ν :=
          integral_mono (hint i).norm (integrable_const _) (hbd i)
      _ = ν.real Set.univ * (B * ‖a i‖) := by simp [integral_const]
  have key := hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : ∀ x, ∑' i, h x * (c i x * a i) = h x * ∑' i, c i x * a i := fun x => tsum_mul_left
  have e2 : ∀ i, ∫ x, h x * (c i x * a i) ∂ν = (∫ x, h x * c i x ∂ν) * a i := fun i => by
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [mul_assoc])
  simp only [e1, e2] at key
  exact key.tsum_eq.symm

theorem parseval {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (hb₀ : b₀.1.det ≠ 0) (a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ)
    (ha : Summable (fun η => ‖a η‖)) (hb : Summable (fun η => ‖b η‖)) :
    ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt η) * a η) *
        conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * b ξ) ∂m.μ =
      ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  classical
  obtain ⟨-, hadd, hnorm, hneg, -, hcont⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (p := p) ψ hψ b₀
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : IsProbabilityMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact m.hμ.2.2⟩
  have hcm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => chv ψ b₀ x (rt η)) := fun η =>
    (hcont.comp (Continuous.prodMk continuous_id continuous_const)).stronglyMeasurable
  have hcm' : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => conj (chv ψ b₀ x (rt ξ))) := fun ξ =>
    Complex.continuous_conj.comp_stronglyMeasurable (hcm ξ)
  have hc1 : ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p), ‖chv ψ b₀ x (rt η)‖ = 1 :=
    fun η x => hnorm x _
  have hc1' : ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p),
      ‖conj (chv ψ b₀ x (rt ξ))‖ = 1 := fun ξ x => by rw [RCLike.norm_conj]; exact hc1 ξ x
  have horth : ∀ ξ η : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) ∂m.μ = if η = ξ then 1 else 0 := by
    intro ξ η
    by_cases h : η = ξ
    · subst h
      have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt η)) * chv ψ b₀ x (rt η) = 1 := fun x => by
        rw [Complex.conj_mul', hc1]; simp
      simp [e]
    · have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) =
          chv ψ b₀ x (rt (η - ξ)) := fun x => by
        have hr : (rt (η - ξ) : Mx D ρ p) = rt η + -rt ξ := by
          rw [← sub_eq_add_neg]; exact rat_sub η ξ
        rw [hr, hadd, hneg, mul_comm]
      simp only [e, if_neg h]
      exact GlobalTheory.T.heisenberg_character_integral_vanishes m ψ hψ b₀ hb₀ (η - ξ) (sub_ne_zero.2 h)
  have hs : ∀ x : Mx D ρ p, Summable fun η => chv ψ b₀ x (rt η) * a η := fun x =>
    Summable.of_norm (by simpa only [norm_mul, hc1, one_mul] using ha)
  have hfm : StronglyMeasurable fun x : Mx D ρ p => ∑' η, chv ψ b₀ x (rt η) * a η :=
    tsum_meas (fun η => (hcm η).mul_const _) hs
  have hfB : ∀ x : Mx D ρ p, ‖∑' η, chv ψ b₀ x (rt η) * a η‖ ≤ ∑' η, ‖a η‖ := fun x => by
    have h1 := norm_tsum_le_tsum_norm (f := fun η => chv ψ b₀ x (rt η) * a η)
      (by simpa only [norm_mul, hc1, one_mul] using ha)
    simpa only [norm_mul, hc1, one_mul] using h1
  have hcoef : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, (∑' η, chv ψ b₀ x (rt η) * a η) * conj (chv ψ b₀ x (rt ξ)) ∂m.μ = a ξ := by
    intro ξ
    have h1 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
      (c := fun (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => chv ψ b₀ x (rt η))
      (h := fun x => conj (chv ψ b₀ x (rt ξ))) (a := a) (B := 1)
      (fun η => (hcm η).aestronglyMeasurable) hc1 (hcm' ξ).aestronglyMeasurable
      (fun x => (hc1' ξ x).le) ha
    simp only [horth, ite_mul, one_mul, zero_mul, tsum_ite_eq] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hconj : ∀ x : Mx D ρ p, conj (∑' ξ, chv ψ b₀ x (rt ξ) * b ξ) =
      ∑' ξ, conj (chv ψ b₀ x (rt ξ)) * conj (b ξ) := fun x => by
    rw [Complex.conj_tsum]; simp only [map_mul]
  have h2 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
    (c := fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => conj (chv ψ b₀ x (rt ξ)))
    (h := fun x => ∑' η, chv ψ b₀ x (rt η) * a η) (a := fun ξ => conj (b ξ))
    (fun ξ => (hcm' ξ).aestronglyMeasurable) hc1' hfm.aestronglyMeasurable hfB
    (by simpa only [RCLike.norm_conj] using hb)
  simp only [hconj, h2, hcoef]

end GlobalTheory.CompanionTheory.FJE
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterOrthogonalityStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenberg_character_orthogonality : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ, Summable (fun η => ‖a η‖) → Summable (fun η => ‖b η‖) → ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt η) * a η) * conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ) * b ξ) ∂m.μ = ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.parseval | exact GlobalTheory.CompanionTheory.FJE.parseval | (intros; apply GlobalTheory.CompanionTheory.FJE.parseval <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLatticeSumsBoundedProduct

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem fold_parseval : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ (Φ φ : Mx D ρ p → ℂ) (B₁ B₂ : ℝ), StronglyMeasurable Φ → StronglyMeasurable φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₁) → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₂) → ∫ v in m.𝓕 ×ˢ m.𝓕, GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v ∂(m.μ.prod m.μ) = ∫ y, Φ y * conj (φ y) ∂m.μ := by
  intro D ρ p m ψ hψ b₀ hb Φ φ B₁ B₂ hΦ hφ h1 h2
  haveI := m.hμ.1
  have hfd : IsAddFundamentalDomain (ratMx D ρ p) m.𝓕 m.μ := m.hμ.2.1
  have hfin : m.μ m.𝓕 = 1 := m.hμ.2.2
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : Countable (ratMx D ρ p) := by
    unfold GlobalTheory.MixModel.ratMx
    exact (AddMonoidHom.rangeRestrict_surjective _).countable
  haveI : MeasurableConstVAdd (ratMx D ρ p) (Mx D ρ p) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  haveI : SFinite m.μ := by
    have hs := hfd.sum_restrict
    open scoped Pointwise in
    haveI : ∀ g : ratMx D ρ p, IsFiniteMeasure (m.μ.restrict (g +ᵥ m.𝓕)) := fun g =>
      ⟨by rw [Measure.restrict_apply_univ, measure_vadd, hfin]; exact ENNReal.one_lt_top⟩
    rw [← hs]
    infer_instance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hfin]; exact ENNReal.one_lt_top⟩
  have hds : ∀ (Ψ : Mx D ρ p → ℂ) (B : ℝ),
      (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Ψ (rt ξ + y)‖) ∧
        ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Ψ (rt ξ + y)‖ ≤ B) →
      ∀ x y, ‖dsum ψ b₀ Ψ x y‖ ≤ B := by
    intro Ψ B hB x y
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).1
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).2
  have hB₁ : 0 ≤ B₁ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h1 0).2
  have hB₂ : 0 ≤ B₂ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h2 0).2
  have hm : StronglyMeasurable (Ap ψ b₀ Φ φ) :=
    (dsum_stronglyMeasurable ψ hψ b₀ Φ hΦ (fun y => (h1 y).1)).mul
      (Complex.continuous_conj.comp_stronglyMeasurable
        (dsum_stronglyMeasurable ψ hψ b₀ φ hφ (fun y => (h2 y).1)))
  have hint : Integrable (Ap ψ b₀ Φ φ) ((m.μ.restrict m.𝓕).prod (m.μ.restrict m.𝓕)) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (B₁ * B₂) (ae_of_all _ (fun v => ?_))
    rw [Ap, norm_mul, Complex.norm_conj]
    exact mul_le_mul (hds Φ B₁ h1 _ _) (hds φ B₂ h2 _ _) (norm_nonneg _) hB₁
  have hP : StronglyMeasurable (fun y => Φ y * conj (φ y)) :=
    hΦ.mul (Complex.continuous_conj.comp_stronglyMeasurable hφ)
  have hsum : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
      ≤ ENNReal.ofReal (B₁ * B₂) := by
    intro y
    calc ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
        ≤ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E,
            ‖Φ (rt ξ + y)‖ₑ * ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := by
          refine ENNReal.tsum_le_tsum (fun ξ => ?_)
          rw [enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj, ofReal_norm]
          gcongr
          exact ENNReal.le_tsum (f := fun η => ‖φ (rt η + y)‖ₑ) ξ
      _ = (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y)‖ₑ) *
            ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal B₁ * ENNReal.ofReal B₂ := by
          gcongr
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h1 y).1]
            exact ENNReal.ofReal_le_ofReal (h1 y).2
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h2 y).1]
            exact ENNReal.ofReal_le_ofReal (h2 y).2
      _ = ENNReal.ofReal (B₁ * B₂) := (ENNReal.ofReal_mul hB₁).symm
  have hPint : Integrable (fun y => Φ y * conj (φ y)) m.μ := by
    refine ⟨hP.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [hfd.lintegral_eq_tsum'']
    beta_reduce
    rw [← lintegral_tsum (f := fun (g : ratMx D ρ p) (x : Mx D ρ p) => ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ)
      (fun g => ((hP.measurable.comp (measurable_const_vadd g)).enorm).aemeasurable)]
    calc ∫⁻ x in m.𝓕, ∑' g : ratMx D ρ p, ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ ∂m.μ
        ≤ ∫⁻ _ in m.𝓕, ENNReal.ofReal (B₁ * B₂) ∂m.μ := by
          refine lintegral_mono (fun x => ?_)
          refine (ENNReal.tsum_le_tsum_comp_of_surjective
            (AddMonoidHom.rangeRestrict_surjective
              (Formalism.L2.Theta.incA D).toAddMonoidHom.mapMatrix) _).trans ?_
          exact hsum x
      _ < ⊤ := by
          rw [lintegral_const, Measure.restrict_apply_univ, hfin, mul_one]
          exact ENNReal.ofReal_lt_top
  rw [← Measure.prod_restrict, integral_prod _ hint, integral_fold m _ hPint]
  refine integral_congr_ae (ae_of_all _ (fun y => ?_))
  exact GlobalTheory.T.heisenberg_character_orthogonality m ψ hψ b₀ hb (fun η => Φ (rt η + y)) (fun η => φ (rt η + y)) (h1 y).1 (h2 y).1

end GlobalTheory.CompanionTheory.FJE
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLatticeSumsBoundedProductStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twisted_lattice_sums_bounded_product : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ (Φ φ : Mx D ρ p → ℂ) (B₁ B₂ : ℝ), StronglyMeasurable Φ → StronglyMeasurable φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₁) → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₂) → ∫ v in m.𝓕 ×ˢ m.𝓕, GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v ∂(m.μ.prod m.μ) = ∫ y, Φ y * conj (φ y) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fold_parseval | exact GlobalTheory.CompanionTheory.FJE.fold_parseval | (intros; apply GlobalTheory.CompanionTheory.FJE.fold_parseval <;> assumption)
end
end
