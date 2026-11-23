module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGiven
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import GroundTheory.LocalFields.Interface
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
public import GroundTheory.LocalFields.LocalFourierChar
public import GroundTheory.LocalFields.LocalFourierHaar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelOfSmallBoxCharacterStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformTwistedInvarianceOnBallStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGivenStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.exists_invertible_matrix_last_line_given : ∀ (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k), a ≠ 0 → ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | exact GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicRestrictionUnipotentSmooth

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_toAdd (n : ℕ) :
    Continuous fun x : Multiplicative (Fin n → k) => colMat k n x.toAdd := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast i =>
      have h : Continuous fun a : Multiplicative (Fin n → k) => Multiplicative.toAdd a i :=
        (continuous_apply i).comp continuous_toAdd
      simpa [colMat] using h
  · simpa [colMat, hj] using continuous_const

theorem continuous_unipMir (n : ℕ) : Continuous (unipMir k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_toAdd n)
  · have h : Continuous fun x : Multiplicative (Fin n → k) => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - colMat k n x.toAdd :=
      continuous_const.sub (continuous_colMat_toAdd n)
    exact h

theorem isSmooth_comp_unipMir : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  intro k _ _ _ _ n V _ _ τ h w
  exact (h w).preimage (continuous_unipMir n)

end GlobalTheory.CompanionTheory.MirFourier

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicRestrictionUnipotentSmoothStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.mirabolic_restriction_unipotent_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | exact GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | (intros; apply GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedBySmallBox

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_box_subset_of_mem_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ N : ℤ, ∀ x ∈ box k n N, Multiplicative.toAdd x ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hball : ∀ i, ∃ N : ℤ, (valBall k N : Set k) ⊆ t i := fun i => by
    obtain ⟨N, -, hN⟩ := (hasBasis_nhds_zero_valBall (K := k)).mem_iff.mp (ht i)
    exact ⟨N, hN⟩
  choose Nf hNf using hball
  refine ⟨((Finset.univ.sup fun i => (Nf i).toNat : ℕ) : ℤ), fun x hx => hsub fun i _ => ?_⟩
  have hle : Nf i ≤ ((Finset.univ.sup fun i => (Nf i).toNat : ℕ) : ℤ) :=
    (Int.self_le_toNat (Nf i)).trans (by exact_mod_cast Finset.le_sup (f := fun i => (Nf i).toNat) (Finset.mem_univ i))
  exact hNf i (valBall_antitone hle ((mem_box k).mp hx i))

theorem exists_box_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ →
    ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  intro k _ _ _ _ n V _ _ ρ hρ v
  have hopen : IsOpen {y : Fin n → k | ρ (Multiplicative.ofAdd y) v = v} := hρ v
  have hU : {y : Fin n → k | ρ (Multiplicative.ofAdd y) v = v} ∈ 𝓝 (0 : Fin n → k) :=
    hopen.mem_nhds (by simp)
  obtain ⟨N, hN⟩ := exists_box_subset_of_mem_nhds k n hU
  exact ⟨N, fun x hx => by simpa using hN x hx⟩

end GlobalTheory.CompanionTheory.MirFourier
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedBySmallBoxStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.smooth_vector_fixed_by_small_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantSmallBoxes

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_mem_twKer_box (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V)
    (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V)
    (hv : v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype)) :
    ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  classical
  have hmem : ∀ x : Multiplicative (Fin n → k), ∃ N : ℤ, x ∈ box k n N := by
    intro x
    choose m hm using fun i => exists_mem_valBall_neg_nat (K := k) (Multiplicative.toAdd x i)
    refine ⟨-((∑ i, m i : ℕ) : ℤ), (mem_box k).2 fun i => ?_⟩
    have h1 := hm i
    have hle : m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
    change normalizedValuation k _ ≤ WithZero.exp (-(-((m i : ℕ) : ℤ))) at h1
    change normalizedValuation k _ ≤ WithZero.exp (-(-((∑ j, m j : ℕ) : ℤ)))
    refine h1.trans (WithZero.exp_le_exp.2 ?_)
    simp only [neg_neg]
    exact_mod_cast hle
  unfold GlobalTheory.PRep.twKer at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, u, rfl⟩ := hx
    obtain ⟨N, hN⟩ := hmem g.1
    exact ⟨N, fun j' hj' => Submodule.subset_span ⟨⟨g.1, box_antitone k n hj' hN⟩, u, rfl⟩⟩
  | zero => exact ⟨0, fun j' _ => Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, fun j' hj' => Submodule.add_mem _ (ha j' (hj'.trans (min_le_left _ _)))
      (hb j' (hj'.trans (min_le_right _ _)))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, fun j' hj' => Submodule.smul_mem _ c (ha j' hj')⟩

end GlobalTheory.CompanionTheory.MirFourier
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantSmallBoxesStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.twisted_invariant_small_boxes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V), v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype) → ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | exact GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMirabolicKernelEqZero

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

theorem eq_zero_of_forall_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  intro k _ _ _ _ ψ hψ hψ1 m V _ _ τ hτ v h0 hg
  have hρ : IsSmooth (τ.comp (unipMir k (m + 1))) := GlobalTheory.T.mirabolic_restriction_unipotent_smooth k (m + 1) V τ hτ
  have hall : ∀ a : Fin (m + 1) → k,
      v ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ a ⊤) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      exact mem_chi_zero ψ τ h0
    · obtain ⟨g, hgr⟩ := GlobalTheory.T.exists_invertible_matrix_last_line_given k m a ha
      have e : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) = a := funext hgr
      have := mem_chi_row ψ τ g (hg g)
      rw [e, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at this
      exact this
  obtain ⟨N, hN⟩ := GlobalTheory.T.smooth_vector_fixed_by_small_box k (m + 1) V _ hρ v
  obtain ⟨J, hJ⟩ := GlobalTheory.T.uniform_twisted_invariance_on_ball k ψ hψ (m + 1) V _ v (addCharConductor ψ - N)
    (fun a => GlobalTheory.T.twisted_invariant_small_boxes k (m + 1) V _ (chi k ψ a) v (hall a))
  exact GlobalTheory.T.twisted_kernel_of_small_box_character k ψ hψ hψ1 (m + 1) V _ hρ v N (min J N) (min_le_right _ _) hN
    (fun a ha => hJ (min J N) (min_le_left _ _) a ha)

end GlobalTheory.CompanionTheory.MirFourier

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMirabolicKernelEqZeroStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.smooth_mirabolic_kernel_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer | exact GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer | (intros; apply GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer <;> assumption)
end
end
