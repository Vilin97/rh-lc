module

public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HpkConjTranspose
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgMulLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Mathlib.Tactic.Linter.Style

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgLeftRight

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgUW

lemma one_mem_UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp [UWset, UH]

theorem omg_left_right : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → ∀ g ∈ B.GV k r, (∀ h ∈ UWset k r z, GlobalTheory.WigSh.omg k r z z' (h * g) = GlobalTheory.WigSh.omg k r z z' (g)) ∧ ∀ h' ∈ UWset k r z', GlobalTheory.WigSh.omg k r z z' (g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hTz hz' hTz' g hg
  refine ⟨fun h hh => ?_, fun h' hh' => ?_⟩
  · have hhU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hii : h⁻¹⁻¹ = h :=
      Matrix.nonsing_inv_nonsing_inv h
        (Matrix.isUnit_det_of_right_inverse (GlobalTheory.WigSh.OmgEquiv.mul_inv hhU))
    have e := GlobalTheory.WigSh.omg_equivariant k r z z' g h⁻¹ 1 hz hTz hz' hTz' hg
      (GlobalTheory.WigSh.OmgEquiv.inv_mem hh) (one_mem_UWset k r z')
    rw [hii, mul_one, inv_one, Matrix.one_mulVec] at e
    exact e
  · have e := GlobalTheory.WigSh.omg_equivariant k r z z' g 1 h' hz hTz hz' hTz' hg
      (one_mem_UWset k r z) hh'
    rw [inv_one, one_mul] at e
    exact e

end GlobalTheory.CompanionTheory.OmgUW
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgNMulN

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmegaBiInv

theorem omg_N_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → inWb k r z' → ∀ g ∈ B.GV k r, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, GlobalTheory.WigSh.omg k r z z' (n * g * n') = GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hz' g hg n hn n' hn'
  rw [Matrix.mul_assoc, GlobalTheory.WigSh.OmLeftN.omg_mul_left k r z z' (g * n') n hz hn]
  exact GlobalTheory.WigSh.omg_mul_N k r z z' g n' hz hz' hg hn'

end GlobalTheory.CompanionTheory.OmegaBiInv
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRep

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgWigEquiv

theorem wigEquiv_omg (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hA : GlobalTheory.WigSh.WigMap k r z' π'' π' d A) (hπ : IsCRepOn (UWset k r z') π'') :
    WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  refine ⟨fun g hg _ n hn n' hn' => ?_, fun g hg _ h hh => ?_, fun g hg _ h hh => ?_⟩
  · exact congrArg A (GlobalTheory.CompanionTheory.OmegaBiInv.omg_N_mul_N k r z z' hz hz' g hg n hn n' hn')
  · exact congrArg A ((GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).1 h hh)
  · have hi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh
    have h1 := (GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).2 h hh
    have h2 := hA.2.1 h⁻¹ hi (GlobalTheory.WigSh.omg k r z z' g)
    have h3 : (π'' h⁻¹).comp (π'' h) = ContinuousLinearMap.id ℂ Wq' := by
      rw [← hπ.2 _ hi _ hh, Formalism.FourierDecayAlt.P.LeftDerivativeCurves.uh_inv_mul hh.1, hπ.1]
      rfl
    show A (GlobalTheory.WigSh.omg k r z z' (g * h)) = (π' h⁻¹).comp ((A (GlobalTheory.WigSh.omg k r z z' g)).comp (π'' h))
    rw [h1, ← ContinuousLinearMap.comp_assoc, ← h2, ContinuousLinearMap.comp_assoc, h3,
      ContinuousLinearMap.comp_id]

end GlobalTheory.CompanionTheory.OmgWigEquiv
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRepStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

theorem _root_.GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → IsCRepOn (UWset k r z') π'' → WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | exact GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | (intros; apply GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg <;> assumption)
end
end
