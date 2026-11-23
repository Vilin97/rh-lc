module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ArEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.BadFinite
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbEll
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbTest
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HkComm
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.MemULOfSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LvEx
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KeepQ
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakAlg
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealAlg
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.WordRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowNorm
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowRep
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealUnivNe
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.REndoOf

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.GenSt

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem genSt : GenSt := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T e₁ e₂
  have hPt := ptOk E a b l₁ l₂ D A
  have hMul := hkMul E a b l₁ l₂ D A S Z L hS hZ
  have hComm := hkComm E a b l₁ l₂ D A S Z L hS hZ
  have hidm : ∀ e e', A.hk S L ∅ e e' = A.idm S L := hMul.2.2.2.2.1
  have hfin : ∀ T' e e', IsFinM (A.hk S L T' e e') := fun T' e e' => (hMul.2.2.2.2.2.2.1 T' e e').1

  have hform : ∀ γ : Gam a b S Z, ∃ wa wb T' e e',
      A.gen S L T e₁ e₂ γ = A.pt wa wb (A.hk S L T' e e') := by
    rintro (_ | x | x | _)
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
  have hok : ∀ γ, (A.gen S L T e₁ e₂ γ).Ok := by
    intro γ
    obtain ⟨wa, wb, T', e, e', h⟩ := hform γ
    rw [h]
    exact hPt.2.2.1 wa wb _ (hfin T' e e')
  refine ⟨⟨hok, ?_, ?_⟩, ?_⟩
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hy (hComm T' T'' e e' f f').1
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    have hop := BlockFiniteConvolution.blkOp₀ E A.blk _ _ hy hy
    rw [ContinuousLinearMap.star_eq_adjoint, ← hop.2.2.2.2.2.1]
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hop.2.2.2.2.1 (hComm T' T'' e e' f f').2
  · haveI : Countable (Pl E) := Small.countable_pl E
    infer_instance

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakRun

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem peakRun : PeakRun := by
  intro E _ _ _ B Q _ χa χb Γ _ t arch a₀ x g ρ hG hK hT hHa hHb ha hv hψ hmul hadj hρ hs
  have hkeep : ∀ y, ∀ f ∈ Q, (t y).op f ∈ Q ∧ star (t y).op f ∈ Q := by
    intro y f hf
    have h1 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y) (t y) (hG.ok y) (hG.ok y)
    obtain ⟨hT1, hR1, -, -, hadjOk, hadjOp, -, -⟩ := h1
    have h2 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y).adj (t y).adj hadjOk hadjOk
    refine ⟨hK _ _ hT1 hR1 f hf, ?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, ← hadjOp]
    exact hK _ _ h2.1 h2.2.1 f hf
  obtain ⟨𝔄⟩ := algEx B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) hG.comm hG.commStar hkeep
  obtain ⟨J, hJ, c, w, hval, hnorm⟩ := peakAlg B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) 𝔄 arch a₀ x ρ ha hv hρ
    (fun s hb hsa => hs (fun y => s (𝔄.ι y)) hsa
      (realAlg E B Q Γ t (fun y => (t y).val χa χb) 𝔄 a₀ g s hG.ok hK hT hb
        (by rw [hsa a₀ ha, hv]; exact one_ne_zero)))
  obtain ⟨R, hR, hrep⟩ := wordRep E B χa χb {γ // arch γ} (fun γ => t γ) (t a₀) J c w hHa hHb (hG.ok a₀)
    (fun γ => ⟨hG.ok γ, hψ γ γ.2⟩) hmul hadj
  refine ⟨_, R, hR, ?_, hnorm⟩
  rw [hval, hv, one_mul] at hrep
  exact hrep

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG

section

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.Zero.ConvolutionTheory.EB

theorem specP (P : Pred) (h : CuspReadP P) : Spec P := rSpec_of peakRun genSt ptOk hkMul repAlg positionTest P (rRead P h)

theorem endoP (P : Pred) (h : CuspReadP P) : EndoP P :=
  rEndo_of arEx lvEx powRep cmbTest cmbEll repAlg powNorm P (specP P h)

theorem stableP (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) (P : Pred) (h : CuspReadP P) :
    StableP P := rStable h2 h3 h5 (cmbPi h1 h4) P (specP P h)

theorem endoBlockG (h : CuspReadI) : EndoBlockG := endoG_of (endoP _ (cuspReadP_inf h))

theorem stableBlockG (h : CuspReadI) (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) : StableBlockG :=
  stableG_of (stableP h1 h2 h3 h4 h5 _ (cuspReadP_inf h))

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
