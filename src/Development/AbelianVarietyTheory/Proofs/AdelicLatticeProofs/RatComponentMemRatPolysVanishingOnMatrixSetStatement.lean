module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRationalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStable

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem evC_map_ringEquiv {ι : Type} (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (σ : ℂ →+* ℂ) f) g = σ (evC f (g.map σ.symm)) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp]; simp

theorem evC_map_rat {ι : Type} (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  unfold evC ev
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem mem_span_vanI_of_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  intro ι _ _ Γ hΓ f hf
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {f | ∀ g ∈ Γ, evC f g = 0}
      add_mem' := by
        intro a b ha hb g hg
        have h1 := ha g hg
        have h2 := hb g hg
        unfold evC at *
        rw [map_add (f := _), h1, h2, add_zero]
      zero_mem' := by
        intro g hg
        simp [evC]
      smul_mem' := by
        intro c a ha g hg
        have h1 := ha g hg
        unfold evC at *
        rw [MvPolynomial.smul_eval, h1, mul_zero] }
  have hrepr : ∀ (p : MvPolynomial (ι × ι) ℂ) k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr p k = AddMonoidAlgebra.coeff p k := fun p k => rfl
  have key := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ) W (by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, ?_, ?_⟩
    · intro g hg
      rw [evC_map_ringEquiv, hw _ (hΓ σ.symm g hg), map_zero]
    · intro k
      rw [hrepr, hrepr, MvPolynomial.coeff_map]
      rfl)
  refine Submodule.span_mono ?_ (key (show f ∈ W from hf))
  rintro w ⟨hw, hq⟩
  have hl : w ∈ Set.range (MvPolynomial.map (σ := ι × ι) (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    simp only [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨k, -, rfl⟩ := hc
    obtain ⟨q, hq⟩ := hq k
    exact ⟨q, by rw [← hrepr, hq]; rfl⟩
  obtain ⟨w₀, rfl⟩ := hl
  refine ⟨w₀, ?_, rfl⟩
  intro g hg
  rw [← evC_map_rat]
  exact hw g hg

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStableStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  first | exact @GlobalTheory.ClassFin.mem_span_vanI_of_vanish | exact GlobalTheory.ClassFin.mem_span_vanI_of_vanish | (intros; apply GlobalTheory.ClassFin.mem_span_vanI_of_vanish <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSet

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_mem_vanI_of_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (l : ℂ →ₗ[ℚ] ℚ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ)) :
    ∀ c : ℂ, ∃ f' ∈ vanI Γ, ∀ m, AddMonoidAlgebra.coeff f' m = l (c * AddMonoidAlgebra.coeff f m) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    intro c
    have hvan : l c • p ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (l c • p) g = 0
      intro g hg
      have h0 : ev p g = 0 := hp g hg
      simp only [ev] at h0 ⊢
      rw [map_smul, h0, smul_zero]
    refine ⟨l c • p, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, mul_comm c,
      ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | zero =>
    intro c
    have hvan : (0 : MvPolynomial (ι × ι) ℚ) ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (0 : MvPolynomial (ι × ι) ℚ) g = 0
      intro g _
      simp [ev]
    exact ⟨0, hvan, fun m => by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, ha, ha'⟩ := hx c
    obtain ⟨b, hb, hb'⟩ := hy c
    have hvan : a + b ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (a + b) g = 0
      intro g hg
      have h1 : ev a g = 0 := ha g hg
      have h2 : ev b g = 0 := hb g hg
      simp only [ev] at h1 h2 ⊢
      rw [map_add (f := _), h1, h2, add_zero]
    refine ⟨a + b, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_add, ha', hb', MvPolynomial.coeff_add, mul_add, map_add (f := _)]
  | smul a x _ hx =>
    intro c
    obtain ⟨f', hf', h'⟩ := hx (c * a)
    exact ⟨f', hf', fun m => by rw [h', MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]⟩

theorem component_mem_vanI : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  intro ι _ _ Γ hΓ f hf l f' hf'
  obtain ⟨p, hp, hpc⟩ :=
    exists_component_mem_vanI_of_mem_span Γ l f (GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable ι Γ hΓ f hf) 1
  have hfp : f' = p := by
    ext m
    rw [hf', hpc, one_mul]
  exact hfp ▸ hp

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSetStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  first | exact @GlobalTheory.ClassFin.component_mem_vanI | exact GlobalTheory.ClassFin.component_mem_vanI | (intros; apply GlobalTheory.ClassFin.component_mem_vanI <;> assumption)
end
end
