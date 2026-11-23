module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFixatorEqUnipotentRadicalMulCommonFixatorStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeMulOfUnipotentCoverDiscreteSubgroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicUnipotentRadicalCoveredByLeviConjugates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionCommuteOfFixesIsotropicColumns
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeMulOfUnipotentCoverDiscreteSubgroupStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.card_le_mul_of_unipotent_cover_discreteSubgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  first | exact @GlobalTheory.SphEis.card_le_mul_of_unip_cover | exact GlobalTheory.SphEis.card_le_mul_of_unip_cover | (intros; apply GlobalTheory.SphEis.card_le_mul_of_unip_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCompactInterUnitaryRationalPoints

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem compact_inter_ratPts_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Set (GAd σ J)),
    IsCompact K → (K ∩ ratPts σ J).Finite := by
  intro F E _ _ _ _ _ σ n J K hK
  have hd : DiscreteTopology (ratPts σ J) := inferInstance
  have hcl : IsClosed ((ratPts σ J : Subgroup (GAd σ J)) : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  exact (hK.inter_right hcl).finite
    (IsDiscrete.mono (isDiscrete_iff_discreteTopology.2 hd) Set.inter_subset_right)

end GlobalTheory.SphEis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCompactInterUnitaryRationalPointsStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.finite_compact_inter_unitaryRationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Set (GAd σ J)), IsCompact K → (K ∩ ratPts σ J).Finite := by
  first | exact @GlobalTheory.SphEis.compact_inter_ratPts_finite | exact GlobalTheory.SphEis.compact_inter_ratPts_finite | (intros; apply GlobalTheory.SphEis.compact_inter_ratPts_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicUnipotentRadicalCoveredByLeviConjugatesStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.isotropicUnipotentRadical_covered_by_levi_conjugates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (V : Set (GAd σ J)) (B : ℝ), IsCompact V ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (GAd σ J), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) ∧ (∀ y ∈ Y, y ∈ unipRad σ J C) ∧ ∀ u ∈ unipRad σ J C, ∃ γ ∈ ratPts σ J, γ ∈ unipRad σ J C ∧ ∃ y ∈ Y, ∃ w ∈ V, w ∈ unipRad σ J C ∧ γ * u = y * lv (tor F E fun i => (μ i : ℤ)) * w * (lv (tor F E fun i => (μ i : ℤ)))⁻¹ := by
  first | exact @GlobalTheory.SphEis.cover_unipRad | exact GlobalTheory.SphEis.cover_unipRad | (intros; apply GlobalTheory.SphEis.cover_unipRad <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionCommuteOfFixesIsotropicColumnsStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.leviSection_commute_of_fixes_isotropicColumns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ α, ∀ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), lv α * x = x * lv α := by
  first | exact @GlobalTheory.SphEis.lv_comm_of_fix_cols | exact GlobalTheory.SphEis.lv_comm_of_fix_cols | (intros; apply GlobalTheory.SphEis.lv_comm_of_fix_cols <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFixatorOfColumnsIsSemidirectLattice

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem semiLat_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ →
    ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C))
      (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))),
      SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ H
  have key : ∀ {P : Subgroup (GAd σ J)}, P ≤ fixG σ J C →
      (ratPts σ J ⊓ fixG σ J C).subgroupOf P = (ratPts σ J).subgroupOf P := fun h => by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩
  obtain ⟨hC, -, cM, cN, hN, hP, hd, hn, -⟩ := GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties F E σ n J j m C D Z J₀ H
  haveI := locallyCompact_unipRad H.cm H.herm hC
  obtain ⟨ν, DN, hν, hDN, h1⟩ := exists_mass_one (cocompact_unipRad H.cm H.herm hC)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := cM.locallyCompactSpace
  have hDM := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom
    ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) Measure.haar
  refine ⟨ν, Measure.haar, DN, _,
    { closedN := cN
      closedM := cM
      norm := fun x hx u hu => (hn x (hP hx.1) u).1 hu
      disj := hd
      dec := ?_
      haarN := hν
      haarM := inferInstance
      domN := by rw [key hN]; exact hDN
      domM := by rw [key inf_le_left]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J j m C D Z J₀ H _ _ inferInstance hDM }⟩
  rintro γ ⟨hγ, hf⟩
  obtain ⟨u, hu, x, hx, e, hr⟩ := GlobalTheory.T.adelicFixator_eq_unipotentRadical_mul_commonFixator F E σ n J j m C D Z J₀ H γ hf
  refine ⟨u, hu, x, hx, ⟨?_, hN hu⟩, ⟨hr hγ, hx.1⟩, e⟩
  have : u = γ * x⁻¹ := by rw [e, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.SphEis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFixatorOfColumnsIsSemidirectLatticeStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.rationalFixatorOfColumns_isSemidirectLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C)) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  first | exact @GlobalTheory.SphEis.semiLat_fixG | exact GlobalTheory.SphEis.semiLat_fixG | (intros; apply GlobalTheory.SphEis.semiLat_fixG <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRationalPointsFixerTorusClassesLe

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_ratPts_fixG_tor_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ B : ℝ, ∀ (μ : Fin j → ℕ) (T : Finset (GAd σ J)), (∀ t ∈ T, t ∈ ratPts σ J) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ fixG σ J C → t = t') → (∀ t ∈ T, ∃ q ∈ fixG σ J C, ∃ w ∈ W, t = q * lv (tor F E fun i => (μ i : ℤ)) * w) → (T.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  obtain ⟨-, hQc, -, -, hNQ, hQP, -, hnorm, hpar⟩ := GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties F E σ n J j m C D Z J₀ hF
  obtain ⟨V, B₁, hV, hcov⟩ := GlobalTheory.T.isotropicUnipotentRadical_covered_by_levi_conjugates F E σ n J j m C D Z J₀ hF lv hlv
  obtain ⟨ν, π, DN, DM, hSL⟩ := GlobalTheory.T.rationalFixatorOfColumns_isSemidirectLattice F E σ n J j m C D Z J₀ hF
  let Λ : Subgroup (GAd σ J) := ratPts σ J ⊓ fixG σ J C
  haveI : DiscreteTopology Λ := inferInstance
  haveI : Countable Λ := inferInstance
  have hDom := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Λ (Measure.haar : Measure (GAd σ J))
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.card_le_mul_of_unipotent_cover_discreteSubgroup (GAd σ J) (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D) Λ (ratPts σ J) (fixG σ J C)
    ν π DN DM Measure.haar _ V W hSL inf_le_left inf_le_right hQc
    (fun q hq => by
      obtain ⟨u, hu, x, hx, e, -⟩ := GlobalTheory.T.adelicFixator_eq_unipotentRadical_mul_commonFixator F E σ n J j m C D Z J₀ hF q hq
      exact ⟨u, hu, x, hx, e⟩)
    (fun K hK => GlobalTheory.T.finite_compact_inter_unitaryRationalPoints F E σ n J K hK) inferInstance hDom hV hW
  refine ⟨B * B₁, fun μ T hT hdist hform => ?_⟩
  set a := lv (tor F E fun i => (μ i : ℤ)) with ha
  obtain ⟨Y, hYc, hYN, hYcov⟩ := hcov μ
  have haP : a ∈ parFlag σ J C (fun _ => 0) := hpar a _ (hlv.onC _)
  have h1 := hB a Y T
    (fun x hx => (GlobalTheory.T.leviSection_commute_of_fixes_isotropicColumns F E σ n J j m C D Z J₀ hF lv hlv _ x hx))
    (fun u => by
      have := hnorm a⁻¹ (inv_mem haP) u
      simpa only [inv_inv] using this)
    hYN
    (fun u hu => by
      obtain ⟨γ, hγ, hγN, y, hy, w, hw, -, e⟩ := hYcov u hu
      exact ⟨γ, ⟨hγ, hNQ hγN⟩, hγN, y, hy, w, hw, e⟩)
    hT
    (fun t ht t' ht' h => hdist t ht t' ht' h.2)
    hform
  calc (T.card : ℝ) ≤ B * Y.card := h1
    _ ≤ B * (B₁ * ∏ i, bse F ^ ((m + j) * μ i)) := mul_le_mul_of_nonneg_left hYc hB0
    _ = B * B₁ * ∏ i, bse F ^ ((m + j) * μ i) := by ring

end GlobalTheory.SphEis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRationalPointsFixerTorusClassesLeStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ B : ℝ, ∀ (μ : Fin j → ℕ) (T : Finset (GAd σ J)), (∀ t ∈ T, t ∈ ratPts σ J) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ fixG σ J C → t = t') → (∀ t ∈ T, ∃ q ∈ fixG σ J C, ∃ w ∈ W, t = q * lv (tor F E fun i => (μ i : ℤ)) * w) → (T.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) := by
  first | exact @GlobalTheory.SphEis.card_ratPts_fixG_tor_le | exact GlobalTheory.SphEis.card_ratPts_fixG_tor_le | (intros; apply GlobalTheory.SphEis.card_ratPts_fixG_tor_le <;> assumption)
end
end
