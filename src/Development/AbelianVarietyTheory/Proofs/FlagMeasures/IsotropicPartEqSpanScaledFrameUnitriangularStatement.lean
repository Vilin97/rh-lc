module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoeffIdealOfLatticeFgAndMemIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealEqOfLocalSpansEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeInfIsotropicEqSumFractionalIdealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanCoefficientIdealEqSpanFrameScaleStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Mathlib.Algebra.AffineMonoid.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoeffIdealOfLatticeFgAndMemIffStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (F : Formalism.MainNotions.S.FlagG S r T) (Λ : Submodule (𝓞 E) S.V) (a : Fin r), Λ.FG → (GlobalTheory.RowLatXS.Ia Λ F a).FG ∧ ∀ t : E, t ∈ GlobalTheory.RowLatXS.Ia Λ F a ↔ ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
  first | exact @GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | exact GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | (intros; apply GlobalTheory.RowLatXS.Ia_fg_and_mem_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealEqOfLocalSpansEqStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fractional_ideal_eq_of_local_spans_eq : ∀ (D : D7) (Z : LocDat D) (I J : Submodule (𝓞 D.host.E) D.host.E), I.FG → J.FG → (∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (I : Set D.host.E)) = Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (J : Set D.host.E))) → I = J := by
  first | exact @GlobalTheory.Sloc.fg_eq_of_completions | exact GlobalTheory.Sloc.fg_eq_of_completions | (intros; apply GlobalTheory.Sloc.fg_eq_of_completions <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeInfIsotropicEqSumFractionalIdealSmulStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.lattice_inf_isotropic_eq_sum_fractionalIdeal_smul : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (G : Formalism.MainNotions.S.Lat.LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (J : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E), (∀ a, J a ≠ 0) → (∀ (a : Fin r) (x : S.V), x ∈ Λ → x ∈ G.fl.Xa (a.val + 1) → G.fl.coefX x a ∈ J a) → (∀ (a : Fin r) (t : E), t ∈ J a → ∃ x ∈ Λ, x ∈ G.fl.Xa (a.val + 1) ∧ G.fl.coefX x a = t) → ∃ e' : Fin r → S.V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ Formalism.MainNotions.S.Lat.XLam Λ G = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
  first | exact @GlobalTheory.RowLatAssembly.xLam_eq_span | exact GlobalTheory.RowLatAssembly.xLam_eq_span | (intros; apply GlobalTheory.RowLatAssembly.xLam_eq_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicPartEqSpanScaledFrameUnitriangular

section

@[expose] public section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem xlam_eq_span_scaled : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ e' : Fin D.R.rS → (VS D).V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ XLam Λ G = Submodule.span (𝓞 D.host.E) {y | ∃ (a : Fin D.R.rS) (x : D.host.E), x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧ y = x • e' a} := by
  intro D T G Z A hA Λ hΛ hloc
  have hdd : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hJ : ∀ a : Fin D.R.rS, GlobalTheory.RowLatXS.Ia Λ G.fl a =
      ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    intro a
    refine GlobalTheory.T.fractional_ideal_eq_of_local_spans_eq D Z _ _ (GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).1
      (FractionalIdeal.fg_of_isNoetherianRing le_rfl _) (fun p => ?_)
    rw [GlobalTheory.T.span_coefficientIdeal_eq_span_frameScale D T G Z A hA Λ hΛ hloc p a]
    have h := Formalism.L2.SG.Pf.locDiffC_holds D Z p a.castSucc
    simp only [Fin.coe_castSucc] at h
    exact h.symm
  obtain ⟨e', he, hX⟩ := GlobalTheory.T.lattice_inf_isotropic_eq_sum_fractionalIdeal_smul (VS D) D.R.rS T G Λ
    (fun a => ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))) (fun a => zpow_ne_zero _ hdd)
    (fun a x hx hxa => by
      have h1 : G.fl.coefX x a ∈ GlobalTheory.RowLatXS.Ia Λ G.fl a :=
        ((GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).2 _).2 ⟨x, hx, hxa, rfl⟩
      rw [hJ a] at h1
      exact h1)
    (fun a t ht => by
      have h1 : t ∈ GlobalTheory.RowLatXS.Ia Λ G.fl a := by rw [hJ a]; exact ht
      exact ((GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).2 t).1 h1)
  exact ⟨e', he, hX⟩

end GlobalTheory.RowLatXS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicPartEqSpanScaledFrameUnitriangularStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicPart_eq_span_scaledFrame_unitriangular : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ e' : Fin D.R.rS → (VS D).V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ XLam Λ G = Submodule.span (𝓞 D.host.E) {y | ∃ (a : Fin D.R.rS) (x : D.host.E), x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧ y = x • e' a} := by
  first | exact @GlobalTheory.RowLatXS.xlam_eq_span_scaled | exact GlobalTheory.RowLatXS.xlam_eq_span_scaled | (intros; apply GlobalTheory.RowLatXS.xlam_eq_span_scaled <;> assumption)
end
end
