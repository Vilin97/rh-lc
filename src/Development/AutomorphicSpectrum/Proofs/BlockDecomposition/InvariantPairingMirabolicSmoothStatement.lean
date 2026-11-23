module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicEvaluationLinear
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInductionStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicEvaluationLinearStatement

section

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_evaluation_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ → EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧ (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ → EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.EvLin.evVal_additive_homogeneous | exact GlobalTheory.CompanionTheory.MirPair.EvLin.evVal_additive_homogeneous | (intros; apply GlobalTheory.CompanionTheory.MirPair.EvLin.evVal_additive_homogeneous <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtensionStatement

section

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_extension : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | exact GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShiftStatement

section

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_shift : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.evVal_conj | exact GlobalTheory.CompanionTheory.MirPair.evVal_conj | (intros; apply GlobalTheory.CompanionTheory.MirPair.evVal_conj <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacter

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Descend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_uM (ψ : AddChar k Circle) (n : ℕ) (u : MirUin k (n + 1)) :
    ∃ y : Fin (n + 1) → k, (u : Mir k (n + 1)) = uM (n + 1) y ∧
      ((mirChar k ψ n u : ℂˣ) : ℂ) = ((ψ (y (Fin.last n)) : Circle) : ℂ) := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp u.2)
  refine ⟨Multiplicative.toAdd w, Subtype.ext hw.symm, ?_⟩
  rw [GlobalTheory.BZMir.mirChar_eq k ψ n u w hw.symm, Circle.toUnits_apply, Units.val_mk0]

theorem left_kill (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (f : V →ₗ[ℂ] ℂ)
    (h : ∀ (y : Fin (n + 1) → k) v, f (T (uM (n + 1) y) v) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * f v) :
    twKer T (MirUin k (n + 1)) (mirChar k ψ n) ≤ LinearMap.ker f := by
  rw [GlobalTheory.PRep.twKer, Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  obtain ⟨y, hu, hχ⟩ := GlobalTheory.CompanionTheory.MirPair.Descend.exists_uM ψ n u
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu, h, hχ, sub_self]

theorem phiMinus_mk (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (p : Mir k n) (v : V) :
    phiMinus k ψ T p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) := rfl

theorem descend : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ n s V V' _ _ _ _ T T' B₀ hT hT' hL hnd
  have hleft : ∀ v' : V', GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker (B₀.flip v') := fun v' =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ T (B₀.flip v') fun y v => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply]
      exact hT y v v'
  have hright : ∀ v : V, GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker (B₀ v) := fun v =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ⁻¹ T' (B₀ v) fun y v' => by
      rw [AddChar.inv_apply]
      exact hT' y v v'
  have h₁ : GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker B₀ := by
    intro v hv
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun v' => ?_
    have h := LinearMap.mem_ker.mp (hleft v' hv)
    rw [LinearMap.flip_apply] at h
    rw [h, LinearMap.zero_apply]
  let B₁ : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] V' →ₗ[ℂ] ℂ :=
    Submodule.liftQ _ B₀ h₁
  have h₂ : GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker B₁.flip := by
    intro v' hv'
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.mem_ker.mp (hright v hv')
  let B' : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] GlobalTheory.PRep.TwJacquet T'
      (GlobalTheory.BZMir.MirUin k (n + 1)) (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ :=
    (Submodule.liftQ _ B₁.flip h₂).flip
  have hB' : ∀ (v : V) (v' : V'), B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B₀ v v' :=
    fun _ _ => rfl
  refine ⟨B', ?_, ?_⟩
  · intro p w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    rw [GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, hB', hB', hL]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ∉ GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
        (GlobalTheory.BZMir.mirChar k ψ n) := fun h =>
      hw ((Submodule.Quotient.mk_eq_zero _).mpr h)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPair.Descend

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacterStatement

section

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.twisted_invariant_pairing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.Descend.descend | exact GlobalTheory.CompanionTheory.MirPair.Descend.descend | (intros; apply GlobalTheory.CompanionTheory.MirPair.Descend.descend <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmooth

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem pairing_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT hT' B hB hnd
  borelize k
  let ν : Measure k := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hinv : TwInv T T' B s := hB
  have hlin := GlobalTheory.T.mirabolic_evaluation_linear ν ψ T B hψ hT
  have hex := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv
  have huniq : ∀ {v v' A A'}, EvVal ν ψ T B v v' A → EvVal ν ψ T B v v' A' → A = A' := by
    rintro v v' A A' ⟨t₀, h₀⟩ ⟨t₁, h₁⟩
    rcases le_total (valuation k (t₀ : k)) (valuation k (t₁ : k)) with h | h
    · rw [← h₀ t₁ h, h₁ t₁ le_rfl]
    · rw [← h₀ t₀ le_rfl, h₁ t₀ h]
  choose f hf using hex
  let B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ f
    (fun v₁ v₂ v' => huniq (hf _ _) (hlin.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.1 _ _ _ _ (hf _ _)))
    (fun v v₁ v₂ => huniq (hf _ _) (hlin.2.2.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.2.2 _ _ _ _ (hf _ _)))
  have hB₀ : ∀ v v', B₀ v v' = f v v' := fun _ _ => rfl
  refine GlobalTheory.T.twisted_invariant_pairing_character ψ n s V V' T T' B₀ ?_ ?_ ?_ ?_
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).1
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).2
  · intro p v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_conductor_shift ν ψ c T T' B s hψ hc hT hT' hinv p v v' _ (hf _ _))
  · intro v hv
    obtain ⟨v', A, hA, hA0⟩ := GlobalTheory.T.mirabolic_pairing_conductor_extension ν ψ c T T' B s hψ hc hT hT' hinv hnd v hv
    exact ⟨v', by rw [hB₀, huniq (hf _ _) hA]; exact hA0⟩

end GlobalTheory.CompanionTheory.MirPair

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmoothStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

theorem _root_.GlobalTheory.T.invariant_pairing_mirabolic_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.pairing_phi | exact GlobalTheory.CompanionTheory.MirPair.pairing_phi | (intros; apply GlobalTheory.CompanionTheory.MirPair.pairing_phi <;> assumption)
end
end
