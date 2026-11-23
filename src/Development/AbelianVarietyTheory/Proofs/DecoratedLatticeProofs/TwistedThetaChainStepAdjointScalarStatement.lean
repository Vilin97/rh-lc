module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEachStepSplitPlaceWithoutExcludedParams
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

-- Source module: Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStageTrivialTwist

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



theorem one_lt_norm (PP : Pl D.host.E) : (1 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
  exact_mod_cast GlobalTheory.LFun.one_lt_absNorm PP

theorem zinv_pos (PP : Pl D.host.E) (a b : ℕ) : 0 < zinv PP a b := by
  refine Finset.prod_pos fun n hn => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_norm PP) ?_))
  have := (Finset.mem_Ioc.1 hn).1
  omega

theorem zinv_mul (PP : Pl D.host.E) {a b c : ℕ} (h : a ≤ b) (h' : b ≤ c) : zinv PP a b * zinv PP b c = zinv PP a c :=
  Finset.prod_Ioc_consecutive _ h h'

theorem idx_vol (PP : Pl D.host.E) (k : ℕ) :
    idxQ PP (k + 1) * volOne PP (k + 1) * zinv PP D.R.t ((k + 1) * D.R.t) = zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) := by
  have h1 : D.R.t ≤ (k + 1) * D.R.t := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have e1 := zinv_mul PP (Nat.zero_le D.R.t) h1
  have e2 := zinv_mul PP (Nat.zero_le D.R.t) (h1.trans (Nat.le_add_left _ D.R.r))
  have p0 := (zinv_pos PP 0 D.R.t).ne'
  have p1 := (zinv_pos PP 0 D.R.r).ne'
  have p2 := (zinv_pos PP D.R.t ((k + 1) * D.R.t)).ne'
  have p3 : (Ideal.absNorm PP.asIdeal : ℝ) ≠ 0 := (zero_lt_one.trans (one_lt_norm PP)).ne'
  unfold idxQ volOne
  rw [← e1, ← e2]
  field_simp

theorem const_eq {c : Com D} {s s' : PiLocalization₂ D} (w : Twist D) (k : ℕ) (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (mR : Measure (GinfC s.V)) (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec) (L H H₀ : ℂ)
    (hH : H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) (h0 : dS w.S₀ s s' ≠ 0)
    (hd : dS (c.S : Set _) s s' = dS w.S₀ s s' * ((∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) : ℝ) : ℂ)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (L * H / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR =
      kapOf w k p m X mR φ v H₀ * L := by
  have e : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) =
      (∏ PP ∈ w.Q, idxQ PP (k + 1)) * (∏ PP ∈ w.Q, volOne PP (k + 1)) * ∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun PP _ => (idx_vol PP k).symm
  have n : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) ≠ 0 :=
    (Finset.prod_pos fun PP _ => zinv_pos PP _ _).ne'
  rw [e] at n
  have n1 : ((∏ PP ∈ w.Q, idxQ PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n2 : ((∏ PP ∈ w.Q, volOne PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n3 : ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul n
  have l : locQ c w k = (∏ PP ∈ w.Q, blockL c k PP) * ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) := by
    rw [locQ, Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [kapOf, hd, e, l, hH, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp

end GlobalTheory.ChainTw.Check

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEachStepSplitPlaceWithoutExcludedParamsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chain_each_step_splitPlace_without_excludedParams : ∀ D : D7, ChainNS D := by
  first | exact @GlobalTheory.ChainNS.chainNS_holds | exact GlobalTheory.ChainNS.chainNS_holds | (intros; apply GlobalTheory.ChainNS.chainNS_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalar

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw

theorem stepLam_of_ns : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  intro D h1 h2 h3 h4 h5 h6 h7 h8
  intro hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' m X hX mR hmR φ v hv H₀ hH₀ hκ B hB u₁ hu hq
  obtain ⟨H, -, hH, -, hL, hol⟩ := h7 c hw.com B hB k hk
  obtain ⟨r1, -, r2, r3⟩ := h8 hG c w hw k hk s s' hs hs' p hp
  have hinv := GlobalTheory.ChainTw.invFam_bounded D c w hw k hk.le s hs u₁ B hu hB
  have hns := GlobalTheory.T.chain_each_step_splitPlace_without_excludedParams D c hw.com c.S subset_rfl B hB hinv k hk
  have hKF : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hv.1, rfl⟩
  have ex := fun u₂ => h6 hG c w hw k hk s s' hs hs' p hp ipD ip hM m X hX mR hmR φ v hv u₁ u₂ _ hu hq hns _ hol
  simp only [GlobalTheory.ChainTw.Check.const_eq w k p m X mR φ v _ H H₀ (r1 H H₀ hH hH₀) r2 r3] at ex
  have hne : p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) ≠ 0 := fun h0 => by
    have e := ex u₁
    rw [h0] at e
    have z : s'.pet 0 0 = 0 := by simp [PiLocalization₂.pet, Lift.pet]
    rw [z] at e
    rcases mul_eq_zero.1 e.symm with e | e
    · exact mul_ne_zero hκ hL ((map_eq_zero _).1 e)
    · have := hM.pos u₁ hu.1
      rw [e] at this
      simp at this
  obtain ⟨v1, v2⟩ := h5 hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ _ hKF
  obtain ⟨w₀, hw0, hadj⟩ := v1 ⟨u₁, hne⟩
  refine ⟨w₀, hw0, hadj, fun x₁ hx₁ => ?_⟩
  have e1 := v2 w₀ hadj u₁ x₁ hx₁
  refine ⟨?_, ?_, fun u₂ x₂ hx₂ => ?_⟩
  · exact (h1 c w hw (k + 1) hk s' hs').2.2.2 x₁ w₀ _ (e1 ▸ hne) (e1 ▸ h2 hG c w hw k hk s s' hs hs' p hp u₁ _ φ hu _ hKF hne)
  · exact (h4 c w hw (k + 1) hk s' hs').1 x₁ w₀ (e1 ▸ hne) (e1 ▸ h3 hG c w hw k hk s s' hs hs' p hp u₁ φ hq _ hKF)
  · have e := ex u₂
    rw [e1, v2 w₀ hadj u₂ x₂ hx₂] at e
    rw [← e]
    exact (hM'.schur x₁ x₂ w₀ w₀).symm

end GlobalTheory.ChainTw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalarStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.twistedThetaChain_step_adjoint_scalar : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  first | exact @GlobalTheory.ChainTw.stepLam_of_ns | exact GlobalTheory.ChainTw.stepLam_of_ns | (intros; apply GlobalTheory.ChainTw.stepLam_of_ns <;> assumption)
end
end
