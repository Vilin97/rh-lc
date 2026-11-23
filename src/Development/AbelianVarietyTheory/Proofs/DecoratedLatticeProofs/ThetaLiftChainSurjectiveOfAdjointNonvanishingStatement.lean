module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveOfAdjointSeparatesLabelledPartsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSet
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewise
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainHeckeParam_add_smul_of_agree_off_set : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  first | exact @GlobalTheory.ChainOnto.isPar_add_smul | exact GlobalTheory.ChainOnto.isPar_add_smul | (intros; apply GlobalTheory.ChainOnto.isPar_add_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewiseStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.ChainOnto.chainPar_inj | exact GlobalTheory.ChainOnto.chainPar_inj | (intros; apply GlobalTheory.ChainOnto.chainPar_inj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishing

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_chainUp : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  intro D hFin hMet hEig hInd hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨hs, hadj⟩ := hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨ipD₀, ip₀, hm₀⟩ := hMet c hc 0 (Nat.zero_le _) s₀ hs₀
  obtain ⟨ipD, ip, hm⟩ := hMet c hc k hk s hs
  haveI : FiniteDimensional ℂ (s₀.CC c) := hFin c hc 0 (Nat.zero_le _) s₀ hs₀
  let Sab := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  let R : GlobalTheory.LFun.Fam D.host.E → GlobalTheory.LFun.Fam D.host.E → Prop := fun B B' => ∀ w ∉ Sab, B w = B' w
  have hRe : Equivalence R :=
    ⟨fun _ _ _ => rfl, fun h w hw => (h w hw).symm, fun h h' w hw => (h w hw).trans (h' w hw)⟩
  have hlin₀ := GlobalTheory.T.thetaChainHeckeParam_add_smul_of_agree_off_set D c s₀
  refine GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts (s₀.CC c) (s.CC c) (GlobalTheory.LFun.Fam D.host.E) (GlobalTheory.LFun.Fam D.host.E) ip₀ ip Θ
    (fun u B => IsPar u B) (fun x B => IsPar x B) R R (fun B => chainPar c B k)
    hm₀.herm hm₀.pos hm.pos hRe (hEig c hc 0 (Nat.zero_le _) s₀ hs₀) hlin₀.1 hlin₀.2 ?_ ?_ ?_
  · intro B B' h w hw
    exact GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise D c k B B' w (h w hw)
  · intro ι x B hx hne
    refine hInd c hc k hk s hs ι x B hx ?_
    intro i i' hii'
    have := hne i i' hii'
    by_contra hcon
    push_neg at hcon
    exact this hcon
  · intro u B hu
    exact hadj ipD₀ ip₀ ipD ip hm₀ hm u B hu

end GlobalTheory.ChainOnto
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  first | exact @GlobalTheory.ChainOnto.ontoAll_of_chainUp | exact GlobalTheory.ChainOnto.ontoAll_of_chainUp | (intros; apply GlobalTheory.ChainOnto.ontoAll_of_chainUp <;> assumption)
end
end
