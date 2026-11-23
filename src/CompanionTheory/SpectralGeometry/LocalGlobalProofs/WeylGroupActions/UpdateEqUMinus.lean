module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGapStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRepStatement
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPolyDegStar
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormSubRight
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBound

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapPolynomialOperator

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigOmgPoly

theorem polyOp_wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → PolyOp (d * (r + 1)) (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hT hz' hT' hA
  exact (GlobalTheory.WigSh.wigMap_omg Wq Wq' k r z z' π' π'' d A hz hT hz' hT' hA).1

end GlobalTheory.CompanionTheory.WigOmgPoly
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapPolynomialOperatorStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

theorem _root_.GlobalTheory.T.wigner_map_polynomial_operator : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → PolyOp (d * (r + 1)) (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg | exact GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg | (intros; apply GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapUpperBound

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigAtOmega

theorem wigUpper_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)),
    inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A →
    WigUpper z z' d (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hT hz' hT' hA g hg
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hT hz' hT' hg
  have h := hA.2.2.2 _ h1 h2
  rw [h3] at h
  exact h

end GlobalTheory.CompanionTheory.WigAtOmega
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapUpperBoundStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

theorem _root_.GlobalTheory.T.wigner_map_upper_bound : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → WigUpper z z' d (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg | exact GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg | (intros; apply GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerPlusMinusDecomposition

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigLowerOmg

theorem wigLower_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (b : ℝ) (n₀ : ℕ) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → (∀ ω, inWb k r ω → herm (Hpk k r) ω z' = 0 → ∀ v : Wq, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2)) → WigLower z z' b n₀ (fun g : B.Mat k r => Ap (GlobalTheory.WigSh.omg k r z z' (g))) (fun g : B.Mat k r => Am (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ _ Wqp _ _ _ Wqm _ _ _ k r z z' b n₀ Ap Am hz hTz hz' hTz' hbound
  unfold WigLower
  intro g hg hGf v
  obtain ⟨hW, hperp, hre⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hTz hz' hTz' hg
  have h := hbound _ hW hperp v
  rw [hre] at h
  have hq : 0 < Gf k r z z' g / Tz k r z' := div_pos hGf hTz'
  have hqn := pow_pos hq n₀
  have key : ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) *
      (‖ContinuousLinearMap.adjoint (Ap (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2 +
        ‖ContinuousLinearMap.adjoint (Am (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2) /
      (Gf k r z z' g / Tz k r z') ^ n₀ := by
    rw [le_div_iff₀ hqn, mul_comm]
    exact h
  refine key.trans (le_of_eq ?_)
  beta_reduce
  rw [← inv_div (Gf k r z z' g) (Tz k r z'), inv_pow]
  ring

end GlobalTheory.CompanionTheory.WigLowerOmg
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerPlusMinusDecompositionStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

theorem _root_.GlobalTheory.T.wigLower_of_adjoint_norm_sq_lower_bound : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (b : ℝ) (n₀ : ℕ) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → (∀ ω, inWb k r ω → herm (Hpk k r) ω z' = 0 → ∀ v : Wq, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2)) → WigLower z z' b n₀ (fun g : B.Mat k r => Ap (GlobalTheory.WigSh.omg k r z z' (g))) (fun g : B.Mat k r => Am (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg | exact GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg | (intros; apply GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.UpdateEqUMinus

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WignerShift

theorem update_eq_uPlus (u : ℕ → ℝ) (l n₀ : ℕ) :
    Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ)) = uPlus u l n₀ := by
  funext i
  unfold uPlus
  rw [Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

theorem update_eq_uMinus (u : ℕ → ℝ) (l n₀ : ℕ) :
    Function.update u l (u l - (n₀ : ℝ)) = uMinus u l n₀ := by
  funext i
  unfold uMinus
  rw [Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

theorem wigExists : WigExists := by
  intro k r z z' Wq _ _ _ π' u l n₀ b hz hz' hT hT' hπ hdec hl1 hlk hgap hb3 hb
  have hreg := GlobalTheory.T.type_exponents_consecutive_gap Wq k r z' π' u hz' hT' hπ hdec
  have h1 := abs_le.mp (hb l (Finset.mem_Icc.mpr ⟨hl1, hlk.le⟩))
  have h2 := abs_le.mp (hb (l + 1) (Finset.mem_Icc.mpr ⟨by omega, hlk⟩))
  have hn : (n₀ : ℝ) ≤ b := by linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, hlow⟩ :=
    GlobalTheory.WigSh.exists_shifted_types_lower_bound Wq k r z' π' u l n₀ b hz' hT' hπ hreg hl1 hlk hgap hb hn
      (by linarith)
  rw [update_eq_uPlus] at hπp
  rw [update_eq_uMinus] at hπm
  exact ⟨{
    Wqp := Vp
    Wqm := Vm
    πp := πp
    πm := πm
    Ap := fun g => Ap (GlobalTheory.WigSh.omg k r z z' g)
    Am := fun g => Am (GlobalTheory.WigSh.omg k r z z' g)
    typeP := hπp
    typeM := hπm
    polyP := GlobalTheory.T.wigner_map_polynomial_operator Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp
    polyM := GlobalTheory.T.wigner_map_polynomial_operator Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm
    equivP := GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp hπp.2.1
    equivM := GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm hπm.2.1
    upperP := GlobalTheory.T.wigner_map_upper_bound Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp
    upperM := GlobalTheory.T.wigner_map_upper_bound Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm
    lower := GlobalTheory.T.wigLower_of_adjoint_norm_sq_lower_bound Wq Vp Vm k r z z' b n₀ Ap Am hz hT hz' hT' hlow }⟩

end GlobalTheory.CompanionTheory.WignerShift
end
end
