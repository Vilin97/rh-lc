module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleOfSemistableCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableCommStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisInclStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRhamStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariantStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActVdRMemTensorDeRhamFiltration

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.FilStable

theorem actVdR_mem_FilV : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (a : ℤ) (g : ↥(GK K))
    (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a →
      actVdR (P.PD K) ρ g y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a := by
  intro l _ P K V _ _ ρ a g y hy
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | tmul v b =>
    exact ⟨ρ g v ⊗ₜ[ℚ_[l]] ⟨(P.PD K).actdR g b.1, (P.PD K).Fil_G g a _ b.2⟩, rfl⟩
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.FilStable
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActVdRMemTensorDeRhamFiltrationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (a : ℤ) (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a → actVdR (P.PD K) ρ g y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a := by
  first | exact @GlobalTheory.FilStable.actVdR_mem_FilV | exact GlobalTheory.FilStable.actVdR_mem_FilV | (intros; apply GlobalTheory.FilStable.actVdR_mem_FilV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqTmulOneOfMonodromyFrobeniusFiltration

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_eq_tmul_one_of_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  intro l _ P AI T ι hι K V _ _ z hN hφ hF
  obtain ⟨w, rfl⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V z).mp hN
  rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V w] at hφ
  have hw := crisIncl_injective P hφ
  have key : ∀ x : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V x) =
      ιV (P.PD K) (LL := ℚ_[l]) (V := V) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ιV, hι, P.PD_ι]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [key] at hF
  obtain ⟨v, rfl⟩ := (GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K ℚ_[l] V).2 w hw hF
  exact ⟨v, by rw [crisIncl_tmul, Polynomial.C_1]⟩

end GlobalTheory.PMon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqTmulOneOfMonodromyFrobeniusFiltrationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  first | exact @GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | exact GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | (intros; apply GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTensorSemistablePeriodRingSurjective

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem monSt_surjective_onto {l : ℕ} [Fact l.Prime] (P : LocPrime l) :
    Function.Surjective (monSt P) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a =>
    have hn : ((n + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    refine ⟨-Polynomial.monomial (n + 1) (((n + 1 : ℕ) : ℚ_[l])⁻¹ • a), ?_⟩
    rw [map_neg, monSt_apply, neg_neg, Polynomial.derivative_monomial, Nat.add_sub_cancel,
      ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem monV_surjective_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V],
      Function.Surjective (monV P ℚ_[l] V) := by
  intro l _ P V _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul v b =>
    obtain ⟨c, rfl⟩ := monSt_surjective_onto P b
    exact ⟨v ⊗ₜ c, monV_tmul P v c⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end GlobalTheory.PMon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTensorSemistablePeriodRingSurjectiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V], Function.Surjective (monV P ℚ_[l] V) := by
  first | exact @GlobalTheory.PMon.monV_surjective_onto | exact GlobalTheory.PMon.monV_surjective_onto | (intros; apply GlobalTheory.PMon.monV_surjective_onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyFrobeniusSolutionFil

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem lTensor_crisIncl_eq_ιV {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR)
    (hι : ∀ b, ι (Polynomial.C b) = P.ιB b) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (w : V ⊗[ℚ_[l]] P.R.B) :
    LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [crisIncl_tmul, LinearMap.lTensor_tmul]
    simp only [ιV, AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply,
      LinearMap.coe_restrictScalars, hι, P.PD_ι]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem solve_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P),
    (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P,
      monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧
      LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  intro l _ P AI T ι hι K V _ _ x y h
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective l P V x
  have he : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀ - z₀ - y) = 0 := by
    have h1 : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀) = (l : ℚ_[l]) • phiV P ℚ_[l] V x := by
      rw [← End.mul_apply, monV_phiV, LinearMap.smul_apply, End.mul_apply, hz₀]
    rw [map_sub, map_sub, h1, hz₀, h, sub_self]
  obtain ⟨u, hu⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mp he
  obtain ⟨x₁, y₁, hy₁, hx₁, hxy⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K ℚ_[l] V).1 u
    (-(LinearMap.lTensor V ι.toLinearMap z₀))
  refine ⟨z₀ + crisIncl P ℚ_[l] V x₁, ?_, ?_, ?_⟩
  · have h0 : monV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) = 0 := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x₁, rfl⟩
    rw [map_add (f := _), hz₀, h0, add_zero]
  · have h2 : phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁ = -crisIncl P ℚ_[l] V u := by
      rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V x₁, ← map_sub, ← hx₁, ← map_neg, neg_sub]
    have h3 : phiV P ℚ_[l] V z₀ - z₀ = crisIncl P ℚ_[l] V u + y := by rw [hu]; abel
    calc phiV P ℚ_[l] V (z₀ + crisIncl P ℚ_[l] V x₁) - (z₀ + crisIncl P ℚ_[l] V x₁)
        = (phiV P ℚ_[l] V z₀ - z₀) + (phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁) := by
          rw [map_add (f := _)]; abel
      _ = y := by rw [h2, h3]; abel
  · rw [map_add (f := _), lTensor_crisIncl_eq_ιV P ι hι K V x₁]
    have : LinearMap.lTensor V ι.toLinearMap z₀ + ιV (P.PD K) (LL := ℚ_[l]) (V := V) x₁ = y₁ := by
      rw [← sub_eq_zero, add_sub_assoc, hxy, add_neg_cancel]
    rw [this]; exact hy₁

end GlobalTheory.PMon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyFrobeniusSolutionFilStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_monodromy_frobenius_solution_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P), (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P, monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧ LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  first | exact @GlobalTheory.PMon.solve_mon_phi_fil | exact GlobalTheory.PMon.solve_mon_phi_fil | (intros; apply GlobalTheory.PMon.solve_mon_phi_fil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocycleOfFrobeniusMonodromyPair

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem GlobalTheory.semistable_class_of_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ x hx y hy hxy
  obtain ⟨ι, hιC, hιact⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hιst, -, -⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hιC hιact K V ρ
  obtain ⟨z, hNz, hφz, hFz⟩ := GlobalTheory.T.exists_monodromy_frobenius_solution_fil l P AI T ι hιC K V x y hxy
  have hx' := (mem_Dst P ρ).mp hx
  have hy' := (mem_Dst P ρ).mp hy
  have hw : ∀ g : ↥(GK K), ∃ v : V, stRep P ρ g z - z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
    intro g
    refine GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration l P AI T ι hιC K V (stRep P ρ g z - z) ?_ ?_ ?_
    · rw [map_sub, ← Module.End.mul_apply, monV_stRep, Module.End.mul_apply, hNz, hx', sub_self]
    · have hφz' : phiV P ℚ_[l] V z = z + y := by rw [← hφz]; abel
      rw [map_sub, ← Module.End.mul_apply, phiV_stRep, Module.End.mul_apply, hφz', map_add (f := _), hy']
      abel
    · rw [map_sub, hιst]
      exact Submodule.sub_mem _ (GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration l P K V ρ 0 g _ hFz) hFz
  choose c hc using hw
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := fun g => (hc g).symm
  exact ⟨z, c, GlobalTheory.T.continuousCocycle_of_semistable_coboundary l P AI T K V ρ hρ z c hc', hc', hNz⟩
end
end
