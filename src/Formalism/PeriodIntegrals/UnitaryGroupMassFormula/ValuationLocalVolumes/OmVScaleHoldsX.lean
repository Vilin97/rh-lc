module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MulTupDiagonal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.MulTupApplyEqSum
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramMulTupHolds

section

@[expose] public section

noncomputable section

namespace PI.NcVal.OmVc1

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale
open scoped TensorProduct

theorem gram_entry {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) (a b : Fin n) :
    gramR R σ J (mulTup D X) a b = (conjT R σ D * gramR R σ J X * D) a b := by

  simp only [gramR, hR, Formalism.UG.hform, mulTup, conjT, Matrix.mul_apply, Matrix.transpose_apply,
  Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  have h1 : ∀ f : Fin M → Fin M → Fin n → Fin n → R ⊗[F] E,
      (∑ i, ∑ j, ∑ l, ∑ k, f i j l k) = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := by
    intro f
    calc _ = ∑ i, ∑ l, ∑ j, ∑ k, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, ∑ k, f i j l k := Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ k, ∑ j, f i j l k :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  refine (h1 _).trans ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramMulTup_holds : GramMulTup := by
  intro F E _ _ _ R _ _ σ n M J D X
  ext a b
  exact gram_entry R σ n M J D X a b

end PI.NcVal.OmVc1
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVLatHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem isCMExt_sig : IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig :=
  ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩

theorem isHermND_J : IsHermND X.B.I.cm.sig X.B.I.J := by
  refine ⟨fun i j => ?_, X.B.I.J_det⟩
  have h := congrFun (congrFun X.B.I.J_herm i) j
  exact h

theorem omVStd_holds : OmVStd X ψ := fun h1 h2 => ⟨isCMExt_sig X, isHermND_J X, h1, h2⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain PI.DegenerateSiegelWeil.Scale PI.NcVal.OmVc2 PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem scl_ne_zero (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : scl X v i ≠ 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [scl, Fin.append_left]; exact OmW.alp_ne_zero v _ _
  · rw [scl, Fin.append_right]; exact inv_ne_zero (OmW.alp_ne_zero v _ _)

theorem scl_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    scl X v (OmW.piv D.R.rS i) = (scl X v i)⁻¹ := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) a
    · rw [OmW.pivot_castAdd_last, scl, Fin.append_left, OmW.alp_last, inv_one]
    · rw [OmW.piv_e, scl, Fin.append_left, Fin.append_right]
  · rw [OmW.piv_f, scl, Fin.append_left, Fin.append_right, inv_inv]

def dU (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)ˣ where
  val := sc (E := X.B.I.E) v (scl X v i)
  inv := sc (E := X.B.I.E) v (scl X v i)⁻¹
  val_inv := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]
  inv_val := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]

theorem dU_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : dU X v (OmW.piv D.R.rS i) = (dU X v i)⁻¹ := by
  apply Units.ext
  show sc (E := X.B.I.E) v (scl X v (OmW.piv D.R.rS i)) = sc (E := X.B.I.E) v (scl X v i)⁻¹
  rw [scl_piv]

theorem yTup_eq (v : PlX X) :
    yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
      (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
  show _ = mulTup (Matrix.diagonal fun i => (dU X v i : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) _
  rw [mulTup_diagonal]
  funext j i
  rfl

theorem gram_ratTup (v : PlX X) :
    gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) = localGramMatrixFrame X u' v := by
  funext a b
  exact OmW.hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ a b

theorem act_mulTup {K : Type} [CommRing K] {a M : ℕ} (g : Matrix (Fin M) (Fin M) K) (f : Fin a → K)
    (Y : Fin a → Fin M → K) :
    (fun j => g.mulVec (mulTup (Matrix.diagonal f) Y j)) = mulTup (Matrix.diagonal f) (fun j => g.mulVec (Y j)) := by
  rw [mulTup_diagonal, mulTup_diagonal]
  funext j i
  show g.mulVec (f j • Y j) i = f j * g.mulVec (Y j) i
  rw [Matrix.mulVec_smul]
  rfl

theorem orbit_eq (v : PlX X) :
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ''
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} := by
  have hc : ∀ k : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J,
      k • yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
        (k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
    intro k
    rw [yTup_eq]
    exact act_mulTup _ _ _
  ext Y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, (hc k).symm⟩
  · rintro ⟨Z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (hc k).symm⟩

theorem omVScale_holds : OmVScale X u' ψ := by
  intro h1 h2 v
  have hS := OmW.omVStd_holds X ψ h1 h2
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := PI.VolStabSW.sigma_invol _ hS.1.2.2.2
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := hS.2.1.1
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [hS.1.2.2.1]; norm_num)
  rw [orbit_eq]
  unfold omAt
  split_ifs with hT
  swap
  · rfl
  unfold omFam
  split_ifs with hfib
  swap
  · rfl
  have := PI.VolStabSW.secondCountable_Fv X.B.I.F v
  have := PI.VolStabSW.locallyCompact_Fv X.B.I.F v
  have : SecondCountableTopology (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))
  have : SecondCountableTopology (HermR (Fv X.B.I.F v) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hEx := PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS
  have hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v)
      (D.R.rS + 1 + D.R.rS) (dX X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dX; rw [dite_eq_left hEx.1]; exact hEx.1.choose_spec
  have hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS)
      (dT X.B.I.cm.sig ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dT; rw [dite_eq_left hEx.2.1]; exact hEx.2.1.choose_spec
  have := hμ.1
  have := hν.1
  have hπ : ∀ i, (Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) ((Function.Involutive.toPerm _
      (OmW.piv_invol D.R.rS)) i) = i := fun i => OmW.piv_invol D.R.rS i
  have hd : ∀ i, dU X v ((Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) i) = (dU X v i)⁻¹ :=
    fun i => dU_piv X v i
  have hfix : hermMap (Fv X.B.I.F v) X.B.I.cm.sig hσ
      ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ⟨localGramMatrixFrame X u' v, hT⟩ = ⟨localGramMatrixFrame X u' v, hT⟩ := by
    apply Subtype.ext
    rw [hermMap_coe]
    show _ * localGramMatrixFrame X u' v * _ = localGramMatrixFrame X u' v
    have hg := OmW.omVGram_holds X u' v
    rw [yTup_eq, PI.NcVal.OmVc1.gramMulTup_holds _ _ _ _ _ _ _ _ _, gram_ratTup] at hg
    exact hg
  have key := fib_image_mulTup X.B.I.cm.sig hσ X.B.I.J hJ (Fv X.B.I.F v) PI.NcVal.OmVc1.gramMulTup_holds
    (PI.VolStabSW.isOpen_units_Fv X.B.I.F v) (lip_field _) _ _ hfib.choose hfib.choose_spec
    (diagUnit (dU X v)) ⟨localGramMatrixFrame X u' v, hT⟩ hfix
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}
  rw [cTup_eq_one (Fv X.B.I.F v) (dU X v) _ hπ hd, cHerm_eq_one X.B.I.cm.sig hσ (Fv X.B.I.F v) (dU X v) _ hπ hd]
    at key
  simp only [ENNReal.coe_one, one_mul] at key
  exact key.symm

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHoldsX

section

@[expose] public section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem omVScale_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVScale X u' ψ :=
  omVScale_holds X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc
end
end
