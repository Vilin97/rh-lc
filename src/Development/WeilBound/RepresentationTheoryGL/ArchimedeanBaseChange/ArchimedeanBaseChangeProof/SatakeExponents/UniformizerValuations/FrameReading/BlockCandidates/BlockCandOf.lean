module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FRGood
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadHalf
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.CandOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)
  {χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ}


theorem cand_of (O : BO F i χ) (ia : ∀ τ, mOf O.χa τ = mOf (F₀.A i).χa τ) (ib : ∀ τ, mOf O.χb τ = mOf (F₀.A i).χb τ)
    (h5 : PreOfTree) (h6 : JoinEx) : ∃ Pa Pb D, F₀.Cand F.d i O.s₁ O.s₂ Pa Pb D := by
  obtain ⟨Pa, ta⟩ := h5 E _ O.s₁ O.good₁ O.untw₁ fun τ => ⟨_, O.inf₁ τ⟩
  obtain ⟨Pb, tb⟩ := h5 E _ O.s₂ O.good₂ O.untw₂ fun τ => ⟨_, O.inf₂ τ⟩
  obtain ⟨D, hJ⟩ := h6 E n _ _ F₀.μ F₀.e Pa Pb F₀.hμ (Nat.add_sub_of_le (F₀.C.le i))
  obtain ⟨j, hj⟩ := Function.ne_iff.1 O.ne
  refine ⟨Pa, Pb, D, ⟨O.good₁, O.good₂, O.untw₁, O.untw₂, ta, tb, hJ⟩, O.leaves₁, O.leaves₂, fun τ => ?_, fun τ => ?_,
    O.F j, O.mem j, hj, O.type j⟩
  · have := O.inf₁ τ
    rw [ia τ] at this
    exact this
  · have := O.inf₂ τ
    rw [ib τ] at this
    exact this

end PositivityTheory.Rg.BcB.F.BC

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.SqNe

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)
  {χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ}


theorem sq_ne (c : F.Γ → ℂ) (hc : c (.inl ()) = 1) (hχ : Chi (fun x => F.g x i) (X F i) c χ) (O : BO F i χ) :
    convF (F.B i).ν ((F.β i).sq (F.m - 1)).ψ O.F ≠ 0 := by
  have e := O.eigX
  intro h0
  rw [h0] at e
  refine smul_ne_zero (div_ne_zero hχ.2.2 (pow_ne_zero _ ?_)) O.ne e.symm
  exact ((hχ.2.1 (.inl ())).trans hc).trans_ne one_ne_zero


theorem eig_h (c : F.Γ → ℂ) (hc : c (.inl ()) = 1) (hχ : Chi (fun x => F.g x i) (X F i) c χ) (O : BO F i χ)
    (x : {w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool) :
    convF (F.B i).ν (F.ψ i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) O.F = c (.inr (.inr x)) • O.F := by
  have e := O.eigFin (.inr (.inr x)) (F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [hχ.2.1 (.inr (.inr x)), hχ.2.1 (.inl ()), hc, div_one] at e
  exact e

end PositivityTheory.Rg.BcB.F.BC

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.QOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)
  {χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ}

def Q : Prop := ∃ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i))
  (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
  F₀.Cand F.d i s₁ s₂ Pa Pb D ∧ (∀ j, G j ∈ pairSpace s₁.space s₂.space) ∧
  (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) ∧
  (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 ∧
  (∀ τ lam, HasWeightAt π τ lam → ∑ k, D.m k τ = infOfWeight lam) ∧
  (∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w)


theorem q_of (hE : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) (hπ : IsAutRepU π) (h : F.Struct)
    (hχ : Chi (fun x => F.g x i) (X F i) (fun x => (F.ug x).p F.fam F.i₀) χ) (h2 : LimAt) (h3 : Ident) (h4 : PowNe)
    (h5 : PreOfTree) (h6 : JoinEx) (h7 : FG.LevRead) (h8 : FG.FRGood) (h9 : FG.FRWeight) : Q F := by
  obtain ⟨O⟩ := h2 hR E n hn π S T F₀ F h i χ hχ
  obtain ⟨ia, ib⟩ := h3 hR E n π S T F₀ F i χ hχ O
  obtain ⟨Pa, Pb, D, hC⟩ := cand_of F i O ia ib h5 h6
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := fun w hw => F.levOff.1 (Finset.mem_coe.2 (Finset.mem_union_left _ hw))
  have hl := fun j => (h7 E n F₀.Sec F.d (F₀.C.a i) (F₀.C.le i) F₀.hSec F.ok hP).2.2 _ _ _ (O.type j)
  have e := h4 E (F.B i) (F.β i) (F.m - 1) _ O.F (h.βok i).ψ (fun j => (hl j).1) (sq_ne F i _ rfl hχ O)
  rw [Nat.sub_add_cancel F.m_pos] at e
  exact ⟨i, O.s₁, O.s₂, Pa, Pb, D, _, O.F, hC, O.mem, hl, e, h9 hR E hE n hn π hπ S F₀ F.d i _ _ _ _ _ hC,
    h8 hR E hE n π hπ S T F₀ F i _ _ Pa Pb D hC.ctx _ O.F O.ne O.mem hl (eig_h F i _ rfl hχ O)⟩

end PositivityTheory.Rg.BcB.F.BC

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.BlockCandOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)
  {χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ}


theorem blockCand_of (h1 : ChiTr) (h2 : LimAt) (h3 : Ident) (h4 : PowNe) (h5 : PreOfTree) (h6 : JoinEx) (h7 : FG.LevRead)
    (h8 : FG.FRGood) (h9 : FG.FRWeight) : BlockCand := fun _ hD E _ _ _ hE n hn π hπ S T F₀ F h =>
  h1 E n π S T F₀.K F₀.W (F.toGenIn hD h) (Q F) rfl fun i _ hχ => q_of F i hE hn hπ h hχ h2 h3 h4 h5 h6 h7 h8 h9

end PositivityTheory.Rg.BcB.F.BC

end
end
end
