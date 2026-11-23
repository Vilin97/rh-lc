module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHeckeCharacterOfClassGroup
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConductorEqTopOfStandardOpen
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import GroundTheory.GlobalFields.TateThesis.HeckeTheoremScaling
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteEmbeddingMemStandardOpenSubgroup
public import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeff
public import GroundTheory.GlobalFields.TateThesis.HeckeChar
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscrNormConductorEqDFOfUnramified

section

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem discrNormConductor_eq_dF_of_unramified :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker → χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  intro F _ _ χ hχ
  have htop : χ.conductor = ⊤ := by
    have h := (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans hχ)
    rw [Ideal.dvd_iff_le, top_le_iff] at h
    exact h
  rw [HeckeCharacter.discrNormConductor, htop, Ideal.absNorm_top, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF]
  simp

end GlobalTheory.CompanionTheory.PartialZeta
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationOfUnramified

section

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem fe_of_parts (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HeckeCharacter F)
    (hD : χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F)
    (hG : ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hG' : ∀ s : ℂ, (χ⁻¹).gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hR : χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * χ.continuedLFunction s =
      χ.coeff (differentIdeal ℤ (𝓞 F)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * (χ⁻¹).continuedLFunction (1 - s)) := by
  have nz : ∀ t : ℂ, (∀ n : ℕ, t ≠ -2 * n) → Complex.Gammaℝ t ≠ 0 := by
    intro t ht h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.1 h0
    exact ht n (by rw [hn]; ring)
  have key := χ.continuedLFunction_functional_equation (s := s)
    (by rw [hG]; exact pow_ne_zero _ (nz s h1))
    (by rw [hG']; exact pow_ne_zero _ (nz _ h2))
  rw [hG, hG', hD, hR] at key
  exact key

end GlobalTheory.CompanionTheory.PartialZeta
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleSectionMemStandardOpenSubgroup

section

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem moduleSection_mem_standardOpenSubgroup {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (t : {r : ℝ // 0 < r}) :
    moduleSection w t ∈ standardOpenSubgroup F := by
  have h1 : ∀ s : {r : ℝ // 0 < r}, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ((moduleSection w s : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro s v
    rw [← coe_finiteProj]
    simp [moduleSection, finiteProj_infiniteEmbedding]
  rw [mem_standardOpenSubgroup]
  intro v
  refine ⟨?_, ?_⟩
  · rw [h1]; exact one_mem _
  · rw [← map_inv, h1]; exact one_mem _

theorem differentiableOn_continuedLFunction :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker →
        DifferentiableOn ℂ χ.continuedLFunction {1}ᶜ := by
  intro F _ _ χ hU
  by_cases h : ∃ τ : ℝ, ∀ x : IdeleGroup F,
      (χ.toIdele x : ℂ) = ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  · obtain ⟨τ, hτ⟩ := h
    let w : InfinitePlace F := Classical.arbitrary _
    have hs : ∀ t : {x : ℝ // 0 < x}, χ.toIdele (moduleSection w t) = 1 := fun t ↦
      MonoidHom.mem_ker.1 (hU (moduleSection_mem_standardOpenSubgroup w t))
    have h0 : archExponent w χ = 0 := archExponent_unique w χ fun t ↦ by simp [hs t]
    have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
    have hd := HeckeCharacter.differentiableOn_continuedLFunction_of_forall hτ
    simpa [hτ0] using hd
  · exact (χ.differentiable_continuedLFunction h).differentiableOn

end GlobalTheory.CompanionTheory.PartialZeta
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardOpenSubgroupLeKerInv

section

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem standardOpenSubgroup_le_ker_inv (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    standardOpenSubgroup F ≤ (χ⁻¹).toIdele.ker := by
  intro x hx
  have hx' : χ.toIdele x = 1 := h hx
  show (χ⁻¹).toIdele x = 1
  rw [HeckeCharacter.toIdele_apply] at hx' ⊢
  change (χ _)⁻¹ = 1
  rw [hx', inv_one]

end GlobalTheory.CompanionTheory.PartialZeta
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumAddCharOfMulMulOfMulInv

section

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem sum_addChar_ofMul_mul_ofMul_inv (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]
    (a b : G) :
    ∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      if a = b then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      ψ (Additive.ofMul (a * b⁻¹)) := by
    intro ψ
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite]
  have hc : Fintype.card (Additive G) = Fintype.card G :=
    Fintype.card_congr Additive.ofMul.symm
  simp only [hc, ofMul_eq_zero, mul_inv_eq_one]

end GlobalTheory.CompanionTheory.PartialZeta
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaFunctionalEquation

section

@[expose] public section

noncomputable section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CompanionTheory.PartialZeta
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

theorem coeff_inv_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (J : (Ideal (𝓞 F))⁰) :
    ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) = ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) := by
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have h1 := coeff_inv_mul_coeff F (classHecke ψ) (standardOpenSubgroup_le_ker ψ) J hJ
  rw [coeff_classHecke ψ J hJ] at h1
  have h2 : ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 J)) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel, ofMul_one, AddChar.map_zero_eq_one]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

def zetaOfClass (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).continuedLFunction s

def zetaOfClassInv (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).continuedLFunction s

theorem isPartialZeta_of_indicator {ι : Type} [Fintype ι] (χ : ι → HeckeCharacter F) (c : ι → ℂ)
    (C : ClassGroup (𝓞 F)) (hU : ∀ i, standardOpenSubgroup F ≤ (χ i).toIdele.ker)
    (horth : ∀ J : (Ideal (𝓞 F))⁰,
      (ClassGroup.mk0 J = C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 1) ∧
      (ClassGroup.mk0 J ≠ C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 0)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (fun s => ∑ i, c i * (χ i).continuedLFunction s) := by
  classical
  refine ⟨?_, fun s hs => ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ => (differentiableOn_continuedLFunction F (χ i) (hU i)).const_mul (c i)
  · have h1 : HasSum (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)))
        (∑ i, c i * (χ i).continuedLFunction s) := by
      refine hasSum_sum fun i _ => ?_
      rw [(χ i).continuedLFunction_eq hs]
      exact ((χ i).hasSum_LFunction hs).mul_left (c i)
    have hfac : ∀ I : Ideal (𝓞 F),
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) =
          (∑ i, c i * (χ i).coeff I) * (Ideal.absNorm I : ℂ) ^ (-s) := fun I => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    let g : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → Ideal (𝓞 F) :=
      fun J => (J.1 : Ideal (𝓞 F))
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext hab)
    have hsupp : ∀ I ∉ Set.range g,
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) = 0 := by
      intro I hI
      by_cases hbot : I = ⊥
      · subst hbot
        simp
      · let J : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hbot⟩
        have hJ : ClassGroup.mk0 J ≠ C := fun h => hI ⟨⟨J, h⟩, rfl⟩
        rw [hfac, show I = (J : Ideal (𝓞 F)) from rfl, (horth J).2 hJ, zero_mul]
    have h2 := (hg.hasSum_iff hsupp).2 h1
    have h3 : (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s))) ∘ g =
        fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s) := funext fun J => by
      simp only [Function.comp_apply]
      rw [hfac, show g J = (J.1 : Ideal (𝓞 F)) from rfl, (horth J.1).1 J.2, one_mul]
    rw [h3] at h2
    exact h2

theorem card_classGroup_ne_zero : (Fintype.card (ClassGroup (𝓞 F)) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem isPartialZeta_zetaOfClass (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClass C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => classHecke ψ) _ C (fun ψ => standardOpenSubgroup_le_ker ψ) fun J => ?_
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if ClassGroup.mk0 J = C then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_classHecke ψ J hJ]
    ring_nf
  rw [e]
  constructor
  · intro h
    rw [if_pos h, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg h, mul_zero]

theorem isPartialZeta_zetaOfClassInv (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClassInv C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => (classHecke ψ)⁻¹) _ C
    (fun ψ => standardOpenSubgroup_le_ker_inv F _ (standardOpenSubgroup_le_ker ψ)) fun J => ?_
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if C = ClassGroup.mk0 J then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_inv_classHecke ψ J, mul_assoc]
  rw [e]
  constructor
  · intro h
    rw [if_pos h.symm, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg (Ne.symm h), mul_zero]

theorem functionalEquation_classHecke [IsTotallyReal F] (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * (classHecke ψ).continuedLFunction s =
      ψ (Additive.ofMul (ClassGroup.mk0 D)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * ((classHecke ψ)⁻¹).continuedLFunction (1 - s)) := by
  have hU := standardOpenSubgroup_le_ker ψ
  have h := fe_of_parts F (classHecke ψ) (discrNormConductor_eq_dF_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ (standardOpenSubgroup_le_ker_inv F _ hU))
    (rootNumber_eq_coeff_different F _ hU) s h1 h2
  rw [← hD, coeff_classHecke ψ _ (nonZeroDivisors.coe_ne_zero D)] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂

theorem GlobalTheory.CompanionTheory.Hypotheses₂.partialZetaFunctionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation := by
  intro F _ _ _ C C' D hD hC
  refine ⟨GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv C',
    GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClassInv C', fun s h1 h2 => ?_⟩
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have h := GlobalTheory.CompanionTheory.Hypotheses₂.functionalEquation_classHecke ψ D hD s h1 h2
  have e : ψ (Additive.ofMul C⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 D)) = ψ (Additive.ofMul C') := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, ← hC, inv_mul_cancel_left]
  calc _ = ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F *
          (GlobalTheory.CompanionTheory.PartialZeta.classHecke ψ).continuedLFunction s) := by ring
    _ = _ := by
      rw [h, ← e]
      ring
end
end
end
