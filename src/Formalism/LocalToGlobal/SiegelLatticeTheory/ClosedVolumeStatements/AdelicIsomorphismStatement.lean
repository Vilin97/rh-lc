module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
public import Formalism.PeriodIntegrals.AdBridgeSteps
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalPointsComparison.BridgeApplyEqOfComp

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealFieldComparison.JmMulApply

section

@[expose] public section

namespace PI.UnitaryGroupMassFormula.BridgeRealK

open Matrix

lemma jm_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl

lemma sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (if ε a then (1 : ℂ) else -1) * (if ε a then (1 : ℂ) else -1) = 1 := by
  cases ε a <;> simp

lemma jm_mul_jm {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 :=
  Formalism.REAL.Jm_mul_self ε

lemma jm_mul_apply {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Formalism.REAL.Jm ε * k) a b = (if ε a then (1 : ℂ) else -1) * k a b := by
  rw [jm_eq, Matrix.diagonal_mul]

lemma mul_jm_apply {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (k * Formalism.REAL.Jm ε) a b = k a b * (if ε b then (1 : ℂ) else -1) := by
  rw [jm_eq, Matrix.mul_diagonal]

lemma comm_iff {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * k = k * Formalism.REAL.Jm ε ↔ ∀ a b, ε a ≠ ε b → k a b = 0 := by
  constructor
  · intro h a b hab
    have e := congrFun (congrFun h a) b
    rw [jm_mul_apply, mul_jm_apply] at e
    cases ha : ε a <;> cases hb : ε b
    · exact absurd (ha.trans hb.symm) hab
    · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at e
      have h2 : (2 : ℂ) * k a b = 0 := by linear_combination -e
      simpa using h2
    · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at e
      have h2 : (2 : ℂ) * k a b = 0 := by linear_combination e
      simpa using h2
    · exact absurd (ha.trans hb.symm) hab
  · intro h
    ext a b
    rw [jm_mul_apply, mul_jm_apply]
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab]; simp

theorem realK : PI.AdBridgeSteps.RealK := by
  intro n ε k hk
  unfold Formalism.REAL.inUJ at hk
  rw [← comm_iff]
  constructor
  · intro hu
    have hu' : k * kᴴ = 1 := mul_eq_one_comm.mp hu
    calc Formalism.REAL.Jm ε * k = (k * kᴴ) * Formalism.REAL.Jm ε * k := by rw [hu', Matrix.one_mul]
      _ = k * (kᴴ * Formalism.REAL.Jm ε * k) := by simp only [Matrix.mul_assoc]
      _ = k * Formalism.REAL.Jm ε := by rw [hk]
  · intro hc
    calc kᴴ * k = kᴴ * k * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by rw [jm_mul_jm, Matrix.mul_one]
      _ = kᴴ * (k * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc]
      _ = kᴴ * (Formalism.REAL.Jm ε * k) * Formalism.REAL.Jm ε := by rw [hc]
      _ = (kᴴ * Formalism.REAL.Jm ε * k) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk, jm_mul_jm]

end PI.UnitaryGroupMassFormula.BridgeRealK
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRealK

section

@[expose] public section

theorem adelic_compact_real_places : PI.AdBridgeSteps.RealK := PI.UnitaryGroupMassFormula.BridgeRealK.realK
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MaximalCompactConjugacy.Assembly

section

@[expose] public section

noncomputable section

namespace PI.BridgeMaxCptWork

open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem conj_unitary_iff {n : ℕ} (P θ : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    ((P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = 1) ↔
      θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ = (P⁻¹)ᴴ * P⁻¹ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hH : Pᴴ * (P⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  have hH' : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPi', Matrix.conjTranspose_one]
  have e1 : (P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1]
  constructor
  · intro h
    calc θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ
        = (P⁻¹)ᴴ * Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * (P * P⁻¹) := by
          rw [hH', hPi', Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h, Matrix.mul_one]
  · intro h
    rw [h, ← Matrix.mul_assoc, hH, Matrix.one_mul, hPi]

theorem kinf_iff (hR : PI.AdBridgeSteps.RealK) (I : AutInst) (e : I.GA ≃ₜ* HAd I)
    (hb : IsBridge I e) (x : I.GA) : (∀ v, x.1 v ∈ KinfV I v) ↔ e x ∈ KinfHA I := by
  have key : ∀ v, (x.1 v ∈ KinfV I v ↔
      ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v * (hmat I (e x)).map (thetaV I v) =
        majV I v) := by
    intro v
    have hu : uMat (x.1 v) = (I.P v)⁻¹ * (hmat I (e x)).map (thetaV I v) * I.P v := (hb x).1 v
    have hP : IsUnit (I.P v) := by
      by_contra hP
      have h0 : (I.P v)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _
        (fun h => hP ((Matrix.isUnit_iff_isUnit_det _).mpr h))
      have hU : IsUnit (uMat (x.1 v)) := Units.isUnit _
      rw [hu, h0, zero_mul, zero_mul] at hU
      haveI : Subsingleton (Matrix (Fin I.n) (Fin I.n) ℂ) :=
        subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hU)
      exact hP (by rw [Subsingleton.elim (I.P v) 1]; exact isUnit_one)
    have hk : Formalism.REAL.inUJ (I.ε v) (uMat (x.1 v)) := (x.1 v).2
    have h1 := hR I.n (I.ε v) (uMat (x.1 v)) hk
    calc x.1 v ∈ KinfV I v ↔ (uMat (x.1 v))ᴴ * uMat (x.1 v) = 1 := h1.symm
      _ ↔ _ := by rw [hu]; exact conj_unitary_iff _ _ hP
  show (∀ v, x.1 v ∈ KinfV I v) ↔ ∀ v, ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v *
    (hmat I (e x)).map (thetaV I v) = majV I v
  exact forall_congr' key

theorem kf_iff (hF : PI.AdBridgeSteps.FinK) (I : AutInst) (e : I.GA ≃ₜ* HAd I)
    (hb : IsBridge I e) (x : I.GA) : x.2 ∈ I.Kset ↔ e x ∈ KfHA I := by
  have h := hF I (e x)
  rw [← (hb x).2] at h
  exact h

theorem mem_KGA_iff (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) (I : AutInst)
    (e : I.GA ≃ₜ* HAd I) (hb : IsBridge I e) (x : I.GA) : x ∈ KGA I ↔ e x ∈ KHA I := by
  show ((∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset) ↔ (e x ∈ KinfHA I ∧ e x ∈ KfHA I)
  exact and_congr (kinf_iff hR I e hb x) (kf_iff hF I e hb x)

theorem bridgeMaxCpt_of (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) :
    ∀ I : AutInst, AdBridgeK I := by
  intro I e hb
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_KGA_iff hR hF I e hb x).1 hx
  · intro hy
    refine ⟨e.symm y, (mem_KGA_iff hR hF I e hb _).2 ?_, by simp⟩
    simpa using hy

end PI.BridgeMaxCptWork
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeMaxCpt

section

@[expose] public section

theorem adelic_maximal_compact : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeK I :=
  PI.BridgeMaxCptWork.bridgeMaxCpt_of adelic_compact_real_places adelic_compact_finite_places
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRatPts

section

@[expose] public section

theorem adelic_rational_points : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement

section

@[expose] public section

namespace Formalism.L2.SG.Closed

theorem AdBridgeIso_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeIso I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_exists (I := I)

theorem AdBridgeGF_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeGF I := adelic_rational_points I

theorem AdBridgeK_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeK I := adelic_maximal_compact I

theorem adelic_isomorphism_statement (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdelicIsomorphism I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_of_parts (I := I) (adelic_rational_points I) (adelic_maximal_compact I)

end Formalism.L2.SG.Closed
end
end
