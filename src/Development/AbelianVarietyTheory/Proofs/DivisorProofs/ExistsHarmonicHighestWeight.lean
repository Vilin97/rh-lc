module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentativeStatement

section

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.exists_fockHarmonic_representative : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) → ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  first | exact @GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | exact GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | (intros; apply GlobalTheory.FockAlg.HarmLift.exists_harm2_rep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicMemFiniteDimensionalCompactStable

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.FockAlg.HarmStable MvPolynomial

namespace GlobalTheory.FockAlg.FinHarm

variable {σ : Type}

def lowDeg (σ : Type) (N : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨆ d : Fin (N + 1), homog σ d

instance [Finite σ] (N : ℕ) : FiniteDimensional ℂ (lowDeg σ N) := by
  haveI : ∀ d : ℕ, FiniteDimensional ℂ (homog σ d) := fun d =>
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  unfold lowDeg
  infer_instance

theorem mem_lowDeg_self (P : MvPolynomial σ ℂ) : P ∈ lowDeg σ P.totalDegree := by
  obtain ⟨N, hN⟩ : ∃ N, N = P.totalDegree := ⟨_, rfl⟩
  rw [← hN]
  have hs := sum_homogeneousComponent P
  rw [← hN] at hs
  rw [← hs]
  refine Submodule.sum_mem _ fun e he => ?_
  have he' : e < N + 1 := Finset.mem_range.1 he
  exact Submodule.mem_iSup_of_mem (⟨e, he'⟩ : Fin (N + 1))
    (homogeneousComponent_mem e P)

theorem DegZero.map_lowDeg {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (N : ℕ)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowDeg σ N) : K P ∈ lowDeg σ N := by
  have hle : lowDeg σ N ≤ (lowDeg σ N).comap K :=
    iSup_le fun d x hx => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem d (hK d x hx))
  exact hle hP

end GlobalTheory.FockAlg.FinHarm

namespace GlobalTheory.FockAlg

open FinHarm

theorem fin_harm : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧
      (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧
      KStable (fockAct2 P Q R S) H0 := by
  intro P Q R S h hh
  have hh' : h ∈ sub2 P Q R S := by
    rw [← SetLike.mem_coe, coe_fockHarmonicsSecondMemberSubmodule]; exact hh
  refine ⟨sub2 P Q R S ⊓ lowDeg _ h.totalDegree, ?_, ⟨hh', mem_lowDeg_self h⟩, ?_, ?_, ?_⟩
  · exact Submodule.finiteDimensional_of_le inf_le_right
  · intro v hv
    rw [← coe_fockHarmonicsSecondMemberSubmodule]; exact hv.1
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct1 hY) _ hw.2⟩
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct2 hY) _ hw.2⟩

end GlobalTheory.FockAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicMemFiniteDimensionalCompactStableStatement

section

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S → ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := by
  first | exact @GlobalTheory.FockAlg.fin_harm | exact GlobalTheory.FockAlg.fin_harm | (intros; apply GlobalTheory.FockAlg.fin_harm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExists

section

@[expose] public section

namespace GlobalTheory

theorem stable_complement_of_kernel_exists
    (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
    (hι : Function.Injective ι) (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ H0) (A : Set (Module.End ℂ V))
    (h1 : ∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0)
    (h2 : ∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0)
    (h3 : ∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) :
    ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧
      ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  intro h hh
  set K : Submodule ℂ V := H0 ⊓ LinearMap.ker pr with hK
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  set K' : Submodule ℂ H := K.map ι with hK'
  haveI : FiniteDimensional ℂ K' := inferInstance
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, e, he, hsum⟩ := K'.exists_add_mem_mem_orthogonal (ι h)
  obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
  have hkH0 : k ∈ H0 := hk.1
  have hkker : pr k = 0 := hk.2
  refine ⟨h - k, H0.sub_mem hh hkH0, by simp [hkker], ?_⟩
  have horth : ∀ k' ∈ K, inner ℂ (ι k') (ι (h - k)) = 0 := by
    intro k' hk'
    have : ι (h - k) = e := by rw [map_sub, hsum]; abel
    rw [this]
    exact (Submodule.mem_orthogonal K' e).mp he _ (Submodule.mem_map_of_mem hk')
  intro a ha z hz
  set c := h - k with hc
  have hcH0 : c ∈ H0 := H0.sub_mem hh hkH0
  set d := a c - z • c with hd
  have hdK : d ∈ K := by
    refine ⟨H0.sub_mem (h1 a ha c hcH0) (H0.smul_mem z hcH0), ?_⟩
    show pr d = 0
    simp [hd, hz]
  obtain ⟨b, hb, hab⟩ := h3 a ha
  have hdorth : ∀ k' ∈ K, inner ℂ (ι k') (ι d) = 0 := by
    intro k' hk'
    have hbk : b k' ∈ K := ⟨h1 b hb k' hk'.1, h2 b hb k' hk'.1 hk'.2⟩
    have e1 : inner ℂ (ι k') (ι (a c)) = 0 := by
      rw [← inner_conj_symm, hab, inner_conj_symm]
      exact horth _ hbk
    rw [hd, map_sub, inner_sub_right, e1, map_smul, inner_smul_right, horth k' hk']
    simp
  have : ι d = 0 := inner_self_eq_zero.mp (hdorth d hdK)
  have hd0 : d = 0 := hι (by rw [this, map_zero])
  exact sub_eq_zero.mp hd0

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExistsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  first | exact @GlobalTheory.stable_complement_of_kernel_exists | exact GlobalTheory.stable_complement_of_kernel_exists | (intros; apply GlobalTheory.stable_complement_of_kernel_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight

section

@[expose] public section

noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.HarmLift

theorem lemA : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W),
    (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := GlobalTheory.T.exists_fockHarmonic_representative

theorem lemB : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧
      KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable

theorem lemC : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 →
    ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) →
      (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) →
      (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) →
      ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel

theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (hZ : IsKC Z) : IsKC (adjZ Z) := by
  intro a b hab
  rw [GlobalTheory.FockAdj.adjZ_apply, hZ b a (fun h => hab (by revert h; rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock])),
    star_zero, mul_zero]

theorem trace_PC {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  simp only [Eab, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e; exact absurd h hcd
  · rfl

end GlobalTheory.HarmLift
end
end
end
