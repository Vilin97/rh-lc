module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepTwistedNormSqEqUntwisted
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepTwistedNormSqEqUntwistedStatement

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
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

theorem _root_.GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (r t j t' : ℕ) (hr : r ≤ S.rank), S.rank + t' = T.rank → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f f' : WO S T → ℂ), IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) χj Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) χj ∅ ξ' f₀ f' → nrm2 m X f = nrm2 m X f' * ∏ PP ∈ Q, (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹) := by
  first | exact @GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors | exact GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors | (intros; apply GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypotheses

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

namespace GlobalTheory.ChainTw.RNrmProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rNrm_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RNrm R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG
  have hL := hG.core.lev
  have hC := hG.core.chain
  have hQ : R.Q A.μ0 = ∅ := GlobalTheory.ChainTw.RModel.Q_base R hL
  have hm := D.R.two_le_m
  intro t
  refine ⟨fun k hk m X hX => ?_, fun m X hX => ?_⟩
  · obtain ⟨c, hc⟩ := hL.βY k (by omega)
    obtain ⟨c', hc'⟩ := hL.βY (k + 1) hk
    have h1 := hC.vY t k hk
    have h2 := hC.vY A.μ0 k hk
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k) :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hrk : (Yc D k).rank + D.R.t = (Yc D (k + 1)).rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), GlobalTheory.Chain.StepVac.rank_Yc (by omega)]; ring
    have key := GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv D R.ψ R.θ (Yc D k) (Yc D (k + 1)) _ _ _ _ _ _ (R.vac k) m X hb hX hc.1 hc'.1
      D.R.r D.R.t k D.R.t (r_le_Y k) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi (k + 1)) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega)]
    congr 4
    simp
  · obtain ⟨c, hc⟩ := hL.βY (D.R.m - 1) (by omega)
    obtain ⟨c', hc'⟩ := hL.βX
    have h1 := hC.vX t
    have h2 := hC.vX A.μ0
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hX' : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
    have hrk : (Yc D (D.R.m - 1)).rank + D.R.t = D.sp.X'.rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), hX']
      obtain ⟨n, hn⟩ : ∃ n, D.R.m = n + 1 := ⟨D.R.m - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel]; ring
    have key := GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' _ _ _ _ _ _ R.vacX m X hb hX hc.1 hc'.1
      D.R.r D.R.t (D.R.m - 1) D.R.t (r_le_Y _) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi D.R.m) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [hX']
    congr 4
    simp

end GlobalTheory.ChainTw.RNrmProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypothesesStatement

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

theorem _root_.GlobalTheory.T.realDatumNormShrink_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RNrm R := by
  first | exact @GlobalTheory.ChainTw.RNrmProof.rNrm_of_given | exact GlobalTheory.ChainTw.RNrmProof.rNrm_of_given | (intros; apply GlobalTheory.ChainTw.RNrmProof.rNrm_of_given <;> assumption)
end
end
