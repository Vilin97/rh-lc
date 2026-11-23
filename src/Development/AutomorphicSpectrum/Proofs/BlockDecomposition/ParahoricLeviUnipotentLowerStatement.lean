module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriLeviUnipotentFactor

section

@[expose] public section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.KOneFactor

open GlobalTheory.LocGL GlobalTheory.LocGL.IwahoriFactor

theorem sub_one_apply_eq_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n)
    {c : GL (Fin n) k} (hc : c ∈ unipRadLower k e) (i j : Fin n)
    (hij : ¬ (e.symm j).1 < (e.symm i).1) : ((c : Matrix (Fin n) (Fin n) k) - 1) i j = 0 := by
  obtain ⟨hP, hD⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).1 hc
  have hB := (GlobalTheory.SmGL.mem_parabLower_iff k).1 hP
  obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective j
  simp only [Equiv.symm_apply_apply] at hij
  rw [Matrix.sub_apply, sub_eq_zero]
  rcases (not_lt.1 hij).lt_or_eq with hab | rfl
  · rw [hB a b p q hab, GlobalTheory.LocGL.IwahoriFactor.one_ne e hab.ne p q]
  · rw [hD a p q, GlobalTheory.LocGL.IwahoriFactor.one_same e a p q]

theorem kone_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ KOne k (Fin n),
    ∃ m : Levi k (fun a => Fin (d a)), leviEmb k e m ∈ KOne k (Fin n) ∧
      ∃ x ∈ unipRad k e ⊓ KOne k (Fin n), ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  intro k _ _ _ _ n s d e g hg
  obtain ⟨c, hc, hgc⟩ := GlobalTheory.LocGL.IwahoriFactor.exists_mul_mem_parab e hg
  have hcP : c ∈ GlobalTheory.SplitWeil.KOne k (Fin n) := by
    first
    | exact hc.2
  have hcl : c⁻¹ ∈ GlobalTheory.SmGL.unipRadLower k e := by
    have hci := inv_mem hc
    first
    | exact hci.1
  obtain ⟨u, hu, hpu⟩ := GlobalTheory.SmGL.exists_levi_mul_unip k e ⟨g * c, hgc⟩
  let m := GlobalTheory.SmGL.leviProj k e ⟨g * c, hgc⟩
  have hpP : leviEmb k e m ∈ KOne k (Fin n) := by
    apply StepData.mem_KOne.2
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst b
      have h := StepData.mem_KOne.1 (mul_mem hg hcP) (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at h
      simpa [Matrix.sub_apply, one_same, m] using h
    · rw [Matrix.sub_apply, GlobalTheory.SmGL.leviEmb_apply_ne k e m hab, one_ne e hab, sub_zero, map_zero]
      exact zero_lt_one
  refine ⟨m, hpP, u, ?_, c⁻¹, ?_, eq_mul_inv_of_mul_eq hpu⟩
  · have hug : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * (g * c) = u := inv_mul_eq_iff_eq_mul.2 hpu
    have huP : u ∈ GlobalTheory.SplitWeil.KOne k (Fin n) := by
      rw [← hug]
      exact mul_mem (inv_mem hpP) (mul_mem hg hcP)
    have hur : u ∈ GlobalTheory.SmGL.unipRad k e := by
      first
      | exact hu
    exact Subgroup.mem_inf.2 ⟨hur, huP⟩
  · show _ ∧ _
    exact ⟨inv_mem hcP, fun i j hij => GlobalTheory.CompanionTheory.KOneFactor.sub_one_apply_eq_zero e hcl i j hij⟩

end GlobalTheory.CompanionTheory.KOneFactor
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriLeviUnipotentFactorStatement

section

@[expose] public section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.iwahori_levi_unipotent_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ KOne k (Fin n),
    ∃ m : Levi k (fun a => Fin (d a)), leviEmb k e m ∈ KOne k (Fin n) ∧
      ∃ x ∈ unipRad k e ⊓ KOne k (Fin n), ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  first | exact @GlobalTheory.CompanionTheory.KOneFactor.kone_factor | exact GlobalTheory.CompanionTheory.KOneFactor.kone_factor | (intros; apply GlobalTheory.CompanionTheory.KOneFactor.kone_factor <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricUnipotentTimesKernel

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.GxSplit

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A K : Subgroup G}
    (hc : ∀ w ∈ A, ∀ g ∈ K, w * g * w⁻¹ ∈ K) {g : G} (hg : g ∈ K ⊔ A) :
    ∃ u ∈ A, ∃ h ∈ K, g = u * h := by
  let H : Subgroup G :=
    { carrier := {g | ∃ u ∈ A, ∃ h ∈ K, g = u * h}
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, h₁, hh₁, rfl⟩ ⟨u₂, hu₂, h₂, hh₂, rfl⟩
        refine ⟨u₁ * u₂, A.mul_mem hu₁ hu₂, (u₂⁻¹ * h₁ * u₂⁻¹⁻¹) * h₂,
          K.mul_mem (hc _ (A.inv_mem hu₂) _ hh₁) hh₂, ?_⟩
        group
      one_mem' := ⟨1, A.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨u, hu, h, hh, rfl⟩
        refine ⟨u⁻¹, A.inv_mem hu, u * h⁻¹ * u⁻¹, hc _ hu _ (K.inv_mem hh), ?_⟩
        group }
  have hle : K ⊔ A ≤ H := sup_le (fun h hh => ⟨1, A.one_mem, h, hh, by simp⟩)
    (fun u hu => ⟨u, hu, 1, K.one_mem, by simp⟩)
  exact hle hg

theorem gx_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ u ∈ unipRad k e ⊓ KO k (Fin n), ∃ h ∈ KOne k (Fin n), g = u * h := by
  intro k _ _ _ _ n s d e g hg
  exact exists_mul_of_mem_sup
    (fun w hw h hh => GlobalTheory.DepthZeroJac.conj_mem_KOne (Subgroup.mem_inf.1 hw).2 hh) hg

end GlobalTheory.CompanionTheory.GxSplit

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricUnipotentTimesKernelStatement

section

@[expose] public section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.parahoric_unipotent_times_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ u ∈ unipRad k e ⊓ KO k (Fin n), ∃ h ∈ KOne k (Fin n), g = u * h := by
  first | exact @GlobalTheory.CompanionTheory.GxSplit.gx_split | exact GlobalTheory.CompanionTheory.GxSplit.gx_split | (intros; apply GlobalTheory.CompanionTheory.GxSplit.gx_split <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricLeviUnipotentLower

section

@[expose] public section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem factor_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ m ∈ (Gx k e).comap (leviEmb k e), ∃ x ∈ unipRad k e, ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  intro k _ _ _ _ n s d e g hg
  obtain ⟨u, hu, h, hh, rfl⟩ := GlobalTheory.T.parahoric_unipotent_times_kernel k n s d e g hg
  obtain ⟨m, hLm, x, hx, c, hc, hdec⟩ := GlobalTheory.T.iwahori_levi_unipotent_factor k n s d e h hh
  have hm : GlobalTheory.SmGL.leviEmb k e m ∈ PositivityTheory.LowerBoundConstant.Gx k e := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.mem_sup_left hLm
  have hconj : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m
      ∈ GlobalTheory.SmGL.unipRad k e := by
    have hn := GlobalTheory.SmGL.leviEmb_mem_normalizer k e m⁻¹
    rw [map_inv] at hn
    have h' := (Subgroup.mem_normalizer_iff.mp hn u).mp hu.1
    rwa [inv_inv] at h'
  refine ⟨m, Subgroup.mem_comap.mpr hm,
    (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m * x,
    mul_mem hconj hx.1, c, hc, ?_⟩
  rw [hdec]; group

end GlobalTheory.CompanionTheory.MoyPrasad
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricLeviUnipotentLowerStatement

section

@[expose] public section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.parahoric_levi_unipotent_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ m ∈ (Gx k e).comap (leviEmb k e), ∃ x ∈ unipRad k e, ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx | exact GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx <;> assumption)
end
end
