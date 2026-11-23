module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
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
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PairingOfPointsExpansion

-- Source module: Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSteps

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.StepsModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


theorem exists_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}
    (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) : ∃ M, IsTermVol t S Φ β M := by
  obtain ⟨M₀, -⟩ := exists_vol G hL t
  have H : ∀ X : Node, ∃ (μ : Measure (GA D (G.V X))) (𝓕 : Set (GA D (G.V X))), (∀ j (h : j < D.R.m) (e : X = .top j), by
        subst e; exact if (Node.top j).neg D.R.m = 0 then IsMeasDef _ (S.levTop t Φ β j h) μ 𝓕
          else Lev.IsMeasFD _ (S.levTop t Φ β j h) μ 𝓕) ∧
      ∀ i (h : i ≤ D.R.m) (e : X = .grid i D.R.m), by
        subst e; exact if (Node.grid i D.R.m).neg D.R.m = 0 then IsMeasDef _ (S.levRow t i h) μ 𝓕
          else Lev.IsMeasFD _ (S.levRow t i h) μ 𝓕 := fun X => by
    by_cases h1 : ∃ j, j < D.R.m ∧ X = .top j
    · obtain ⟨j, hj, rfl⟩ := h1
      have hV := node_isV G hL (X := .top j) hj.le
      obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levTop W t Φ β hj)
      refine ⟨μ, 𝓕, fun j' h e' => ?_, fun _ _ e' => by cases e'⟩
      cases e'; exact e
    · by_cases h2 : ∃ i, i ≤ D.R.m ∧ X = .grid i D.R.m
      · obtain ⟨i, hi, rfl⟩ := h2
        have hV := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
        obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levRow W t hi)
        refine ⟨μ, 𝓕, fun _ _ e' => (by cases e'), fun j' h e' => ?_⟩
        cases e'; exact e
      · exact ⟨0, ∅, fun j h e => absurd ⟨j, h, e⟩ h1, fun i h e => absurd ⟨i, h, e⟩ h2⟩
  choose ν fd hν using H
  exact ⟨⟨ν, fd, M₀.νN, M₀.fdN⟩, fun j h => (hν _).1 j h rfl, fun i h => (hν _).2 i h rfl⟩

end GlobalTheory.RowClaim.StepsModel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetsOfOrthogonalSum

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.JetsAssembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem defTot_eq_sum {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M σ τ φ F = σ.sum fun P c => c * defTot t S M (Finsupp.single P 1) τ φ F := by
  unfold defTot
  refine Finsupp.sum_congr fun P _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d _ => ?_
  ring

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetsOne (ch : Choice R) : Prop :=
  ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y,
      defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) =
        κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y)

theorem jetsAt_of_one (ch : Choice R) (hL : R.toLevCh.Is A.μ0) (h : JetsOne ch) : JetsAt ch := by
  refine ⟨fun t Φ β => StepsModel.exists_isTermVol ch.S.toGridChoice hL t Φ β, fun σ => ?_⟩
  choose κ hκ using h
  refine ⟨σ.sum fun P c => c * κ P, fun t a β hβ M τ hM hτ y => ?_⟩
  rw [defTot_eq_sum, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [hκ P t a β hβ M τ hM hτ y, mul_assoc]

end GlobalTheory.RowClaim.JetsAssembly

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedJetSuccEqAssembly

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
namespace GlobalTheory.RowClaim.JetsAssembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {T : Type}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
theorem twisted_jet_one_of_all : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun ch => JetsOne ch := _root_.GlobalTheory.T.twisted_pairing_identity
theorem twistedJet_succ_eq_assembly : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → StepJets := by
  intro hP hS
  obtain ⟨C0, H⟩ := _root_.GlobalTheory.RowClaim.JetsAssembly.twisted_jet_one_of_all hP hS
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  exact ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j =>
    jetsAt_of_one ch s.core.lev (H D large₂ e hx Γ Pl0 T A Ks R F s ch i j)⟩
end GlobalTheory.RowClaim.JetsAssembly
end
end

section
open GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.twisted_jets_assemble : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → StepJets := by
  first | exact @_root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly | exact _root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly | (intros; apply _root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly <;> assumption)
end
end
end
