module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsLow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicReadingLastStepTrivialOffLevel
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicDataStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueCompletionMatrixOfRationalTwistAutStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationValue
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousOfCond

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicReadingLastStepTrivialOffLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_adelicReading_lastStep_trivial_off_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → Nonempty (Unique (Ch B.R.m)) → ∃ A' : TwDat I l Z u a Ch, A'.Is ∧ (∀ i, i < B.R.m → ∀ β, A'.kb i β = A.kb i β) ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A'.kb B.R.m β) = 1 := by
  first | exact @GlobalTheory.AdForm.TopMove.exists_twDat_top_trivial | exact GlobalTheory.AdForm.TopMove.exists_twDat_top_trivial | (intros; apply GlobalTheory.AdForm.TopMove.exists_twDat_top_trivial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUniqueStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isPointOfDecoratedLattice_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E)) (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  first | exact @GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | exact GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | (intros; apply GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleAdelicDataStandardBasePoints

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm



theorem exists_twDat_baseStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (Ch : ℕ → Type) (_ : ∀ i, Fintype (Ch i)) (A : TwDat I l Z u a Ch), A.Is ∧ Nonempty (Unique (Ch B.R.m)) ∧ (∀ i, Nonempty (Idx I.sel (I.tup a) (I.idx a) i) → Nonempty (Ch i)) ∧ GlobalTheory.QTw.BaseCommon A ∧ (∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i)) ∧ ∀ i, i ≤ B.R.m → ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → (i < B.R.m ∨ ¬ I.UnderQ a v) → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1 ∧ ∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i) := by
  intro B X I hI hP l Z u a
  obtain ⟨Ch, hF, A, hA, hU, hk⟩ := GlobalTheory.T.exists_tupleChain_adelicData I hI hP l Z u a
  obtain ⟨A₁, hA₁, hk₁, hm₁⟩ := GlobalTheory.T.exists_adelicReading_lastStep_trivial_off_level I hI hP l Z u a Ch A hA hU
  have hkb : ∀ i, i ≤ B.R.m → ∀ β β', A₁.kb i β = A₁.kb i β' := by
    intro i hi β β'
    rcases Nat.lt_or_eq_of_le hi with h | rfl
    · rw [hk₁ i h, hk₁ i h, hk i h, hk i h]
    · obtain ⟨hu⟩ := hU
      rw [hu.uniq β, hu.uniq β']
  let A₂ : TwDat I l Z u a Ch := { A₁ with
    kA := fun i β => A₁.kA i (Classical.choice ⟨β⟩)
    xr := fun i β => A₁.xr i (Classical.choice ⟨β⟩) }
  have hA₂ : A₂.Is := by
    refine { hA₁ with kA := fun i hi β => ?_ }
    obtain ⟨h1, h2, h3⟩ := hA₁.kA i hi (Classical.choice ⟨β⟩)
    refine ⟨h1, ?_, h3⟩
    rw [h2, hkb i hi]
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  refine ⟨Ch, hF, A₂, hA₂, hU, ?_, ?_, ?_, ?_⟩
  · intro i ⟨b⟩
    have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
    obtain ⟨p, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := i) (Formalism.L2.Col.DecoF.base _ _ _ _ _)
    exact ⟨A₂.chOf i ((I.stp u a i).cl b p)⟩
  · intro i hi β β'
    refine ⟨?_, rfl, rfl⟩
    have e1 := (hA₁.base i hi β).1
    have e2 := (hA₁.base i hi β').1
    rw [hkb i hi β β'] at e1
    exact GlobalTheory.T.isPointOfDecoratedLattice_unique _ _ _ _ (IsPtOf.of_extTo (I.Q_subset_SQ a) hd e1) (IsPtOf.of_extTo (I.Q_subset_SQ a) hd e2)
  · intro i hi β
    exact (hk₁ i hi β).trans (hk i hi β)
  · intro i hi β v hv hq
    refine ⟨?_, fun i hi β => (hk₁ i hi β).trans (hk i hi β)⟩
    rcases hq with h | h
    · show Formalism.UG.bc _ (A₁.kb i β) = 1
      rw [hk₁ i h, hk i h]
      exact (MemChart.kStd_spec l.pr u _).2.1 v hv
    · rcases Nat.lt_or_eq_of_le hi with h' | rfl
      · show Formalism.UG.bc _ (A₁.kb i β) = 1
        rw [hk₁ i h', hk i h']
        exact (MemChart.kStd_spec l.pr u _).2.1 v hv
      · exact hm₁ β v hv h

end GlobalTheory.AdForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleAdelicDataStandardBasePointsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_tupleAdelicData_standardBasePoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (Ch : ℕ → Type) (_ : ∀ i, Fintype (Ch i)) (A : TwDat I l Z u a Ch), A.Is ∧ Nonempty (Unique (Ch B.R.m)) ∧ (∀ i, Nonempty (Idx I.sel (I.tup a) (I.idx a) i) → Nonempty (Ch i)) ∧ GlobalTheory.QTw.BaseCommon A ∧ (∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i)) ∧ ∀ i, i ≤ B.R.m → ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → (i < B.R.m ∨ ¬ I.UnderQ a v) → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1 ∧ ∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i) := by
  first | exact @GlobalTheory.AdForm.exists_twDat_baseStd | exact GlobalTheory.AdForm.exists_twDat_baseStd | (intros; apply GlobalTheory.AdForm.exists_twDat_baseStd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentatives

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

theorem idxIsProd_of_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  intro X Pr R Ch sel S₀ mu cst L G s hL hP j hj hh hex
  have hrefl : ∀ (i : ℕ) (P : rowSG Pr sel mu) (a : AutY X R i), SameDC (Pr := Pr) cst.sharp i P.1 a a :=
    fun i P a => ⟨1, one_mem _, 1, one_mem _, by simp⟩
  rcases j with _ | i
  · obtain ⟨b, hb⟩ := hL.zero_uniq
    refine ⟨b, fun P => ?_, fun b' _ => hb b'⟩
    obtain ⟨b₀, hb₀⟩ := hex P
    rw [← hb₀, hL.zero_h, hL.zero_h]
  · have hi : i < s := by omega
    choose bP hbP using hex
    obtain ⟨b, hb⟩ := hL.surj i hi hh
      (fun P hPg => hbP P ▸ hL.stabG (i + 1) (bP P) P hPg)
      (fun P hPg => hbP P ▸ hL.boundQ (i + 1) (bP P) P hPg)
      (fun P => by
        obtain ⟨al, hal⟩ := hL.nonvan i hi (bP P) P
        exact ⟨al, hbP P ▸ hal⟩)
    refine ⟨b, fun P => ?_, fun b' hb' => ?_⟩
    · have h1 := hb P
      rw [← hbP P] at h1 ⊢
      exact hP (i + 1) b (bP P) P h1
    · refine hL.inj i hi b' b (fun P => ?_)
      have e : L.h (i + 1) b' P = L.h (i + 1) b P := by
        have h1 := hb P
        rw [hb' P, ← hbP P] at *
        exact (hP (i + 1) b (bP P) P h1).symm
      rw [e]; exact hrefl _ _ _

end GlobalTheory.TwBridge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentativesStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  first | exact @GlobalTheory.TwBridge.idxIsProd_of_ok | exact GlobalTheory.TwBridge.idxIsProd_of_ok | (intros; apply GlobalTheory.TwBridge.idxIsProd_of_ok <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsLow

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LowJoin
open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
section Place
variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}
end Place

theorem exists_quadratic_extension_readsLow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ ha hc t
  have hI := hW.tr.ok
  have hm := B.R.two_le_m
  obtain ⟨Ch₀, -, A, hA, hlast, hne, -, hstd, -⟩ := GlobalTheory.T.exists_tupleAdelicData_standardBasePoints I hI hW.tr.pins.some l Z u (W.P.I.tup t)
  have hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (_root_.GlobalTheory.Fam.chrK_alt W t j) (I.C.mu0 ⟨j, hj⟩ * I.xi (W.P.I.tup t)) := fun j hj =>
    GlobalTheory.Mem.TupChar.chrEq_mul (hW.tr.chr ⟨j, hj⟩) (hW.tq.xi t)
  let e := ((_root_.GlobalTheory.Fam.pk_z W).Q t).equivFin
  let pl : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → Pl (I.rec7 l Z).host.E := fun i => (e.symm i).1
  have mem : ∀ i, pl i ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t := fun i => (e.symm i).2
  have plinj : Function.Injective pl := Subtype.val_injective.comp e.symm.injective
  have plsurj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, pl i = PP := fun PP h => ⟨e ⟨PP, h⟩, by simp [pl]⟩
  let P : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → BadPr I (W.P.I.tup t) := fun i => ⟨pl i, Finset.mem_union_right _ ((hW.tq.Q t _).1 (mem i))⟩
  have hoff : ∀ i, (P i).1 ∉ (B.primes X).vGs := fun i => TC.Q_notMem_of_ok hI _ _ ((hW.tq.Q t _).1 (mem i))
  let G := fun i => a.Q (pl i) ⟨t, mem i⟩
  have hs : ∀ i, (G i).s + 1 + 1 = B.R.m := fun i => (G i).hs
  choose E hψ sg hE using fun i => exists_good hI hW.tr.tw (P i) (hoff i) (G i) rfl hc ha.pinX.std (_root_.GlobalTheory.Fam.chrK_alt W t) hχ
  let Rel : ∀ i j, Formalism.L2.Col.AutY B.fields B.R j → (E i).Ch j → Prop := fun i j γ y => ∀ d (h : j + d = (G i).s),
    IsGL (X := B.fields) (R := B.R) (k := (G i).k) ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y)
  have hrel : ∀ i j d (h : j + d = (G i).s) γ y, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
      ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y) → Rel i j γ y := fun i j d h γ y h1 d' h' => by
    obtain rfl : d' = d := by omega
    exact h1
  have hd : ∀ i j, j ≤ B.R.m - 2 → ∃ d, j + d = (G i).s := fun i j hj => ⟨(G i).s - j, by have := hs i; omega⟩
  have hbij := exists_bij (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hI.ch_ok hI.sel_ok (hI.sharp _) (hI.idx_ok (W.P.I.tup t))
    (GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives _ _ _ _ _ _ _ _ _ _ _ (hI.idx_ok _) (idxProd hI hW.tr.tw _)) (h_one hW.tr.tw _) P
    (fun i i' h => plinj (congrArg (fun Q : BadPr I (W.P.I.tup t) => Q.1) h)) hoff
    (fun Q hQ => (plsurj Q.1 ((hW.tq.Q t _).2 ((Finset.mem_union.1 Q.2).resolve_left hQ))).imp fun i h => Subtype.ext h)
    (fun i => (E i).Ch) Rel
    (fun i j hj b => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_completionMatrix_of_rationalTwistAut B.fields B.R (G i).k ((G i).q.pr.comp (incA (I.rec7 l Z))) j (d + 1)
        (by have := hs i; simp only [Formalism.L2.Col.cOf]; omega) ((I.idx _).h j b (P i))
      obtain ⟨y, -, rfl⟩ := ((E i).rep_bij j d h).surjOn (((hE i).rat j d h ⟨b⟩).ge ⟨b, hg⟩)
      exact ⟨y, hrel i j d h _ _ hg⟩)
    (fun i j hj h0 y => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨b, hb⟩ := ((hE i).rat j d h h0).le (((E i).rep_bij j d h).mapsTo (Set.mem_univ y))
      exact ⟨b, hrel i j d h _ _ hb⟩)
    (fun i j hj γ γ' y y' h1 h2 => by
      obtain ⟨d, h⟩ := hd i j hj
      exact (isGL_unique (h1 d h) (h2 d h)).trans
        ⟨fun e => ((E i).rep_bij j d h).injOn (Set.mem_univ _) (Set.mem_univ _) e, fun e => e ▸ rfl⟩)
    (fun i j hj h0 ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      exact (hE i).next j d h h0 ⟨_, ((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)⟩)
    (fun i j hj ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      obtain ⟨g, hg, -⟩ := Set.mem_iUnion₂.1
        (((E i).reps.bij j d h).mapsTo (((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)))
      obtain ⟨y', -, -⟩ := ((E i).rep_bij j _ _).surjOn hg
      exact ⟨y'⟩)
  have hup : ∀ j, B.R.m ≤ j → ∀ i, Nonempty (Unique ((E i).Ch j)) := fun j hj i => by
    rcases hj.eq_or_lt with h | h
    · rw [← h, ← hs i]
      exact Fintype.card_eq_one_iff_nonempty_unique.1 (E i).one
    · exact (hE i).up j (by rw [hs i]; exact h)
  have key : ∀ j, ∃ (π : ∀ i, Ch₀ j → (E i).Ch j) (ι : (∀ i, (E i).Ch j) → Ch₀ j),
      (∀ i d (h : j + d = (G i).s) (hj : j < B.R.m) β, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
        ((G i).q.pr.comp (incA (I.rec7 l Z))) ((I.idx (W.P.I.tup t)).h j ((A.b0 j β).get hj) (P i)) ((E i).rep j d h (π i β))) ∧
      (j + 1 ≠ B.R.m → (∀ y i, π i (ι y) = y i) ∧ (j ≤ B.R.m → Function.Surjective ι)) := by
    intro j
    rcases lt_trichotomy (j + 1) B.R.m with hj | hj | hj
    · obtain ⟨φ, h1, h2⟩ := hbij j (by omega)
      let f := Equiv.ofBijective _ (h1.comp (get_bij hA j hj))
      exact ⟨fun i β => f β i, f.symm, fun i d h _ β => h2 _ i d h, fun _ =>
        ⟨fun y i => congrFun (f.apply_symm_apply y) i, fun _ => f.symm.surjective⟩⟩
    · have h1 : ∀ i, Nonempty ((E i).Ch j) := fun i => by
        rw [show j = (G i).s + 1 by have := hs i; omega]
        exact ⟨((E i).cos_all 0 (zero_mem _)).choose⟩
      have h2 : Nonempty ((I.idx (W.P.I.tup t)).β j) := by
        rw [show j = B.R.m - 2 + 1 by omega]
        exact ⟨(hI.idx_ok _).last_uniq.choose⟩
      exact ⟨fun i _ => (h1 i).some, fun _ => (hne j ⟨Idx.of h2.some (by omega)⟩).some,
        fun i d h => by have := hs i; omega, fun h => absurd hj h⟩
    · have h1 := fun i => (hup j (by omega) i).some
      refine ⟨fun i _ => default, fun _ => (hne j ⟨Idx.top _ _ _ (by omega)⟩).some, fun i d h hj' => by omega,
        fun _ => ⟨fun y i => Subsingleton.elim _ _, fun hj' β => ⟨default, ?_⟩⟩⟩
      obtain rfl : j = B.R.m := by omega
      exact hlast.some.instSubsingleton.elim _ _
  choose π ι k1 k2 using key
  refine ⟨⟨Ch₀, A, _, pl, mem, E, P, hψ, sg, fun i j => π j i, ι⟩, hA, plinj, plsurj,
    fun j hj => (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (hA.chr ⟨j, hj⟩) (hχ j hj), fun i => ?_, fun _ => rfl,
    fun i => (hE i).sign, fun i => (hE i).tw, fun i => (hE i).M, fun i j => k1 j i, hstd, hlast, fun j _ hj => (k2 j hj).1,
    fun j hj y y' h => funext fun i => ?_, (k2 0 (by omega)).2 (by omega), (k2 _ (by omega)).2 le_rfl,
    fun j hj hj' γ hγ => absurd ((k2 _ hj').2 hj γ) hγ⟩
  · exact res_of_tw hI (hE i).tw (hW.lev.2.2 t ▸ hW.pk.bot.hyp.2.2.2.1.lev.xiR t _ (mem i))
  · exact ((k2 j hj).1 y i).symm.trans ((congrArg (π j i) h).trans ((k2 j hj).1 y' i))
end GlobalTheory.LowJoin
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsLowStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_quadratic_extension_reads_low_of_true : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  first | exact @_root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | exact _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | (intros; apply _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow <;> assumption)
end
end
end
