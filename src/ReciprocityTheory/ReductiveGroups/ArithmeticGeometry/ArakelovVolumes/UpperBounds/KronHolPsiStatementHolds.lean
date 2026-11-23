module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigCellPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.EtaStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfT
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfC

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem FrameMeasStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FrameMeasStatement (E := E) :=
  @GlobalTheory.FrameMeasureClosed.frameMeas_holds E _ _ _

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix
open scoped Matrix ComplexOrder ENNReal

noncomputable section

theorem SumBoundStatement_holds : SumBoundStatement := by
  intro f p q s hs Γ hd hU
  obtain ⟨c, hc, hsepΓ⟩ := sumBd_sep Γ hd hU
  obtain ⟨C, hC, hbound⟩ := sumBd_sum (p := p) (q := q) (f := f) hs hc
  refine ⟨C, hC, fun v hv => ?_⟩
  choose G hG hGw using fun k => sumBd_frame (hv k)
  let x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fun γ k =>
    ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k
  have hxU : ∀ a k, IsUpq (x a k) := fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)
  have hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
    intro a b hab
    have hmem : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)
    obtain ⟨k, i, j, hk⟩ := hsepΓ _ hmem hne
    refine ⟨k, i, j, le_of_le_of_eq hk ?_⟩
    have : x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      simp only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]
    rw [this]
  calc ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s)
      = ∑' γ : Γ, ENNReal.ofReal (∏ k, (Complex.normSq (det (x γ k).toBlocks₂₂))⁻¹ ^ s) := by
        congr 1; funext γ
        rw [Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]
    _ ≤ C := hbound Γ x hxU hxsep

end
end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bigCellStatement_holds : BigCellStatement (E := E) := bigCell_of (lu_holds (E := E))

theorem kaUnfoldStatement_holds : KaUnfoldStatement (E := E) :=
  kaUnfold_of (measInv_holds (E := E)) SumBoundStatement_holds

theorem pairUnfoldStatement_holds : PairUnfoldStatement (E := E) :=
  PairUnfoldPf.pairUnfold_of (measInv_holds (E := E)) kaUnfoldStatement_holds (lu_holds (E := E))

theorem extFStatement_holds : ExtFStatement (E := E) :=
  extF_of (lu_holds (E := E)) (FrameMeasStatement_holds (E := E))

theorem onto_of_poin_extF (hPoin : PoinStatement (E := E)) (hExtF : ExtFStatement (E := E)) :
    OntoStatement (E := E) :=
  onto_of hPoin hExtF (RGF.rhGradF_holds (E := E)) (exhaustG_holds (E := E)) kaUnfoldStatement_holds
    pairUnfoldStatement_holds bigCellStatement_holds (OFC.omFConn_of_cm (E := E))

theorem kronHolPsiStatement_holds : KronHolPsiStatement (E := E) :=
  kronHolPsi_of_frameMeas (FrameMeasStatement_holds (E := E))

theorem interp_of_poin (hP : PoinStatement (E := E)) : InterpStatement (E := E) :=
  interp_of hP kronHolPsiStatement_holds

theorem interpC_of_poin (hP : PoinStatement (E := E))
    (hη : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
      ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
          leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ) :
    InterpCStatement (E := E) := interpC_of hP kronHolPsiStatement_holds hη

theorem ontoStatement_holds : OntoStatement (E := E) :=
  onto_of_poin_extF (poin_holds (E := E)) extFStatement_holds

theorem interpStatement_holds : InterpStatement (E := E) := interp_of_poin (poin_holds (E := E))

theorem interpC_of_eta (hη : EtaStatement (E := E)) : InterpCStatement (E := E) :=
  interpC_of_poin (poin_holds (E := E)) hη

theorem interpCStatement_holds : InterpCStatement (E := E) := interpC_of_eta (EtaPf.eta_holds (E := E))

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end
