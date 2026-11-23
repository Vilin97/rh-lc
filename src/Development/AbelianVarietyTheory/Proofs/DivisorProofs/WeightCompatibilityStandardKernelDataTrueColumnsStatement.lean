module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairLeIffPairHtLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGapStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTieRec

section

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare

theorem mem_tops_rec (D : D7) (z : Bool × Formalism.MainNotions.G.HH D) :
    tauPl D z ∈ topsOf D.host D.eTau ↔ z.1 = false ∧ z.2 ∈ D.host.TT := by
  classical
  have hinj := D.R.toFrame.tau1_injective
  have hP := factPlaces D.R.toFrame
  have h0 : (D.eTau (tauPl D z) : D.R.GG) = Formalism.MainNotions.G.plGG D z := by simp [tauPl]
  unfold topsOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h0]
  unfold Host.topPlaces
  rw [Finset.mem_image]
  obtain ⟨b, t⟩ := z
  constructor
  · rintro ⟨t', ht, h⟩
    cases b <;> simp only [Formalism.MainNotions.G.plGG, if_true, if_false, Bool.false_eq_true] at h
    · exact ⟨rfl, (hinj h) ▸ ht⟩
    · exact absurd h (hP.2 _ _)
  · rintro ⟨h1, h2⟩
    refine ⟨t, h2, ?_⟩
    simp only at h1
    simp [Formalism.MainNotions.G.plGG, h1]

end GlobalTheory.ColumnNormCompare
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightTieTrueCols

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem weightTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), DelNat (I.rec7 l Z) → ∀ u : B.Word, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (numDatumOfParameters (I.rec7 l Z) L) (X := B.fields) (Pr := B.primes X) B.wts (plRec (I.rec7 l Z)) u (codeRec L u) := by
  intro B X I _ l Z L hD u
  obtain ⟨n, hn⟩ := hD
  have hfl : ((⌊(I.rec7 l Z).s.Del⌋₊ : ℕ) : ℚ) = (I.rec7 l Z).s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨B.wts_isOk, fun z => ?_, fun z => ⟨?_, fun i => ?_⟩⟩
  · exact GlobalTheory.ColumnNormCompare.mem_tops_rec (I.rec7 l Z) z
  · exact B.wts_isOk.hc_row u _
  · change ((I.rec7 l Z).hcW u (plRec (I.rec7 l Z) z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < (I.rec7 l Z).R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < (I.rec7 l Z).R.k
    · rw [dite_eq_left h]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk : k < (I.rec7 l Z).R.k - 2 := by omega
      have a := (I.rec7 l Z).s.u_letter u (plRec (I.rec7 l Z) z) k hk
      have hv := (I.rec7 l Z).hcW_v u (plRec (I.rec7 l Z) z)
      rw [a, hv, ← hfl]
      rfl
    · rw [dite_eq_right h]
      by_cases h0 : i = 0
      · subst h0
        exact (I.rec7 l Z).hcW_first u _ hi'
      · have h1 : i = (I.rec7 l Z).R.k - 1 := by omega
        subst h1
        exact (I.rec7 l Z).hcW_last u _ (by omega)

end GlobalTheory.CoreHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)

noncomputable section

namespace GlobalTheory.ColRows



theorem weightTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
  obtain ⟨hX, -, hPr, -, -, -, hword, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  subst hX
  cases hPr
  cases hword
  cases hW
  have hN := GlobalTheory.T.columnNormParameters_eq_natStepGap (I.rec7 l Z) L Del h0 hDel hEta
  refine ⟨plRec (I.rec7 l Z), fun u => ?_⟩
  have key := GlobalTheory.CoreHt.weightTie_trueCols I hOk l Z L ⟨Del, hDel⟩ u
  have gen : ∀ N : NumDatum, numDatumOfParameters (I.rec7 l Z) L = N → ∀ (W' : Wts B.fields (B.primes X).Word N.R), HEq B.wts W' →
      ∀ (pl' : RPl N.R ≃ B.fields.Tau), HEq (plRec (I.rec7 l Z)) pl' → ∀ δ : Code N, HEq (codeRec L u) δ →
      GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie N (X := B.fields) (Pr := B.primes X) W' pl' u δ := by
    intro N hN W' hW' pl' hpl δ hδ
    subst hN
    cases hW'
    cases hpl
    cases hδ
    exact key
  exact gen _ hN _ HEq.rfl _ HEq.rfl _ HEq.rfl

end GlobalTheory.ColRows

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  first | exact @GlobalTheory.ColRows.weightTie_of_stdKer | exact GlobalTheory.ColRows.weightTie_of_stdKer | (intros; apply GlobalTheory.ColRows.weightTie_of_stdKer <;> assumption)
end
end
