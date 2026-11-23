module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionYZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLamEqPsiSuperSumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMatrixMemLevelZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalProperty
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjMemRowsIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTraceMemStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.SymChain.SymData.RowLam

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_sum_sum_lt {ι κ' : Type} [Fintype ι] [Fintype κ'] (f : ι → κ' → k)
    (hf : ∀ i j, valuation k (f i j) < 1) : valuation k (∑ i, ∑ j, f i j) < 1 := by
  apply Valuation.map_sum_lt _ one_ne_zero
  intro i _
  exact Valuation.map_sum_lt _ one_ne_zero (fun j _ => hf i j)

theorem psi_inv_mul_eq_one (ψ : AddChar k Circle) (ϖ : kˣ) (hψ : GlobalTheory.SplitWeil.HasConductor ψ 1)
    (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {t : k} (ht : valuation k t < 1) :
    ψ (((ϖ⁻¹ : kˣ) : k) * t) = 1 := by
  have h1 := (hψ 1).2 (by simp)
  apply h1
  have hle : valuation k t ≤ valuation k (ϖ : k) := (hϖ t).1 ht
  rw [map_mul, map_one]
  calc valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k t
      ≤ valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k (ϖ : k) := by gcongr
    _ = 1 := by rw [← map_mul]; simp

end GlobalTheory.SymChain.SymData.RowLam

open GlobalTheory.SymChain.SymData.RowLam in
theorem GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  intro k _ _ _ _ s κ S x M hM hsup
  have hS := S.sym.2 x
  have hsimple : valuation k (GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k)) < 1 := by
    unfold GlobalTheory.RootEx.simpleSum
    apply val_sum_sum_lt
    intro i j
    split_ifs with h
    · exact hsup i j h
    · simp
  have hdiff : valuation k (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ -
      ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) < 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    apply val_sum_sum_lt
    intro a b
    split_ifs with h
    · simpa [Matrix.toBlocks₁₁] using hM a b
    · simp
  have e1 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hsimple
  have e2 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hdiff
  have e3 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁) =
      S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) := by
    rw [mul_sub, AddChar.map_sub_eq_div] at e2
    exact div_eq_one.mp e2
  rw [hS, e1, e3]
  simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.symmetricLevelCharacter_eq_addChar_superdiagSum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  first | exact @GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near | exact GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near | (intros; apply GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalVector

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.FamTraceChiCol


open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain in
theorem conj_embX_toBlocks₂₂ {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((typeFrame ϖ ord).bas⁻¹ * embX c g * (typeFrame ϖ ord).bas).val.toBlocks₂₂ = 1 := by
  have e1 : (typeFrame ϖ ord).bas.val = fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val := rfl
  have e2 : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val := by
    change (embA n _)⁻¹.val = _
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, show (embX c g).val = fromBlocks g.val 0 0 1 from rfl,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Units.inv_mul]

end GlobalTheory.FamTraceChiCol

noncomputable section
namespace GlobalTheory.FamTraceChiCol


end GlobalTheory.FamTraceChiCol
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameClose

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTraceChiCol
end GlobalTheory.FamTraceChiCol
noncomputable section
namespace GlobalTheory.FamTraceChiCol

theorem frame_close_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → ∀ (i : Fin a.n) (x : (a.G i).S.P.J), (∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r), p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E, Ideal.Quotient.mk (a.pl i).1.asIdeal z = (_root_.GlobalTheory.FamTraceChi.reductionYZero_alt W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' → valuation (a.G i).k (((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) → ∀ g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → (∀ p q : Fin (I.rec7 l Z).R.k, valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inl p) (Sum.inl q) - g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q))) < 1) ∧ ∀ p q : Fin ((a.G i).s + 1), q.val = p.val + 1 → valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inr p) (Sum.inr q)) < 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ y hy hyU i x hx g hg
  obtain ⟨hV, hG⟩ := ha.tie row col
  have hrJ := (_root_.GlobalTheory.T.true_geometry_local_data_alt W hW u a ha hat row col hc κ hκ y hy).1 hyU
  have hb : a.g.b 0 ∈ GfC (Yc (I.rec7 l Z) 0) := by
    have h1 := ha.vis.b 0
    rw [hV.b 0] at h1
    exact h1
  have hxe : embA a.d.B.d a.d.B.o κ ∈ GfC ((I.rec7 l Z).sp.Y 0) := GlobalTheory.Corev.EmbAGfC.embA_mem_GfC_fin _ _ _ _ _ _ _ _ κ hκ
  have hSt := ((_root_.GlobalTheory.FamTrace.Rows.mem_rJ_iff_finE_mem_St_and_block_mem W _ (mul_mem (mul_mem (inv_mem hb) hxe) hb)).1 hrJ).1
  obtain ⟨e, he, hM⟩ := hG.frame i 0 ((a.G i).s + 1) (Nat.zero_add _)
  have hid := (hG.idem i).1
  have hn : (Yc (I.rec7 l Z) 0).rank = (I.rec7 l Z).R.r := by
    rw [(I.rec7 l Z).sp.Y_rank _ (min_le_right _ _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  have hr : (I.rec7 l Z).R.r ≤ (Yc (I.rec7 l Z) 0).rank := hn.ge
  have hmi : 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := by
    have h1 := (a.G i).hs
    have h2 := (a.G i).S.odd
    unfold Ranks.rS; omega
  have hbes : (ofSplit (a.G i).q).IsBesFrame a.d.B.lev ((a.G i).sc 0) ((a.G i).FX 0 (Nat.zero_le _))
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) := by
    have key : ∀ Bl : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, Bl = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ hmi →
        ∀ (FA : Frame (a.G i).k Bl.A.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0))
          (F : Frame (a.G i).k Bl.V.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1))), HEq FA ((a.G i).FX 0 (Nat.zero_le _)) →
          HEq F ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) → (ofSplit (a.G i).q).IsBesFrame Bl ((a.G i).sc 0) FA F := by
      rintro Bl rfl FA F h1 h2
      cases h1; cases h2
      exact (a.G i).bes 0 _ hmi _ _
    exact key _ (ha.bot.1 hmi) _ _ HEq.rfl HEq.rfl
  have hm := GlobalTheory.TraceAtG.mat_embA_besFrame (ofSplit (a.G i).q) a.d.B.lev _ _ _ hbes κ g hg
  let σ := e.symm.trans (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _))
  have key := GlobalTheory.SeeSaw.LevRed.red_of_movedTo (a.G i).q (a.pl i).1 hid _ _ _ _ _
    (((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
      GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
      ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.submatrix σ σ) hM ?_ hSt
  swap
  · have hs : ∀ (A : Matrix (Fin (Yc (I.rec7 l Z) 0).rank) (Fin (Yc (I.rec7 l Z) 0).rank) (a.G i).k)
        (M : Matrix (Fin (Yc (I.rec7 l Z) 0).rank) (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1)) (a.G i).k),
        A * M.submatrix id σ = (A * M).submatrix id σ := fun A M => by
      ext r c'; simp [Matrix.mul_apply]
    have e1 : ((Formalism.L2.Theta.mt (Yc (I.rec7 l Z) 0) ((embA a.d.B.d a.d.B.o) κ)).map (a.G i).q.pr) *
        ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β =
        ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β * (GlobalTheory.RootEx.embX ((a.G i).s + 1) g).val := by
      have hm' : (Formalism.L2.Theta.mt (Yc (I.rec7 l Z) 0) ((embA a.d.B.d a.d.B.o) κ)).map (a.G i).q.pr =
          ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β * (GlobalTheory.RootEx.embX ((a.G i).s + 1) g).val *
            ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).γ := hm
      rw [hm', Matrix.mul_assoc, Matrix.mul_assoc, Frame.γβ, Matrix.mul_one]
    refine Eq.trans (hs _ _) ?_
    refine Eq.trans ?_ (Matrix.submatrix_mul_equiv _ _ id σ σ).symm
    rw [← Matrix.mul_assoc, e1, Matrix.mul_assoc, ← Units.val_mul]
    congr 1
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel_left]
  have hidx : ∀ (p : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a' : Fin (I.rec7 l Z).R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → e.symm (Fin.castLE hr a') = .inl p := fun p a' ha => by
    rw [Equiv.symm_apply_eq]
    refine Fin.ext ?_
    rw [he]
    rcases p with p | p <;> exact ha
  have main : ∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r),
      p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q →
      valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val p q -
        (((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val
            (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _) (.inl p))
            (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _) (.inl q)))) < 1 := by
    intro p q p' q' hp hq
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((_root_.GlobalTheory.FamTraceChi.reductionYZero_alt W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ *
      embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q')
    have h1 := hx p q p' q' hp hq z hz
    have h2 := key (Fin.castLE hr p') (Fin.castLE hr q') z (by
      rw [hz]; exact congrFun (congrFun (GlobalTheory.SeeConjReord.rankBlock_val_eq_submatrix_of_le_rank hr hn.le _) p') q')
    simp only [Matrix.submatrix_apply, σ, Equiv.trans_apply, hidx p p' hp, hidx q q' hq] at h2
    have e : ∀ s t w : (a.G i).k, s - t = (s - w) + -(t - w) := fun s t w => by ring
    rw [e _ _ ((ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E))]
    exact Valuation.map_add_lt _ h1 (by rw [Valuation.map_neg]; exact h2)
  refine ⟨fun p q => ?_, fun p q hpq => ?_⟩
  · have hpr : p.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; unfold Ranks.r; omega
    have hqr : q.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; unfold Ranks.r; omega
    have h := main (.inl p) (.inl q) ⟨p.val, hpr⟩ ⟨q.val, hqr⟩ rfl rfl
    have h11 := GlobalTheory.LevX.conj_embX_val (a.G i).S.ϖ
      (stdOrd (Fin (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k) (Fin (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)) g
    have h11' := congrFun (congrFun h11 (.inl (.inl p))) (.inl (.inl q))
    rw [GlobalTheory.StepData.stdOrd_eps, GlobalTheory.StepData.stdOrd_eps] at h
    exact h11' ▸ h
  · have hpr : (I.rec7 l Z).R.k + p.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; have := p.2; unfold Ranks.r; omega
    have hqr : (I.rec7 l Z).R.k + q.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; have := q.2; unfold Ranks.r; omega
    have h := main (.inr p) (.inr q) ⟨_, hpr⟩ ⟨_, hqr⟩ rfl rfl
    have h22 := conj_embX_toBlocks₂₂ (a.G i).S.ϖ
      (stdOrd (Fin (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k) (Fin (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)) g
    have h22' := congrFun (congrFun h22 p) q
    have hne : p ≠ q := fun h => by rw [h] at hpq; omega
    rw [Matrix.one_apply_ne hne] at h22'
    have hs1 : ∀ r : Fin ((a.G i).s + 1), stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)
        (.inl (.inr r)) = .inr r := fun r => GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block _ _ 0 _ _ r
    rw [hs1, hs1] at h
    change valuation (a.G i).k (_ - ((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.toBlocks₂₂ p q) < 1 at h
    have e0 : ((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.toBlocks₂₂ p q = 0 := h22'
    rw [e0, sub_zero] at h
    exact h
end GlobalTheory.FamTraceChiCol
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameCloseStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.true_geometry_final_vector_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → ∀ (i : Fin a.n) (x : (a.G i).S.P.J), (∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r), p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E, Ideal.Quotient.mk (a.pl i).1.asIdeal z = (_root_.GlobalTheory.FamTraceChi.reductionYZero_alt W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' → valuation (a.G i).k (((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) → ∀ g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → (∀ p q : Fin (I.rec7 l Z).R.k, valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inl p) (Sum.inl q) - g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q))) < 1) ∧ ∀ p q : Fin ((a.G i).s + 1), q.val = p.val + 1 → valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inr p) (Sum.inr q)) < 1 := by
  first | exact @_root_.GlobalTheory.FamTraceChiCol.frame_close_alt | exact _root_.GlobalTheory.FamTraceChiCol.frame_close_alt | (intros; apply _root_.GlobalTheory.FamTraceChiCol.frame_close_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LamEqColLam

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamTraceChiCol
theorem lam_eq_colLam_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → ∀ (i : Fin a.n) (x : (a.G i).S.P.J), (∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r), p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E, Ideal.Quotient.mk (a.pl i).1.asIdeal z = (_root_.GlobalTheory.FamTraceChi.reductionYZero_alt W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' → valuation (a.G i).k (((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) → (((a.G i).S.P.lam x : ℂˣ) : ℂ) = GlobalTheory.FamTraceChiCol.colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ y hy hyU i x hx
  obtain ⟨g, hg⟩ : ∃ g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g :=
    ⟨coordHom _ (a.G i).q.pr _ _ ((a.G i).FX 0 (Nat.zero_le _)).βγ ((a.G i).FX 0 (Nat.zero_le _)).γβ κ,
      (eq_coordHom_iff _ _ _ _ _ _ κ _).2 rfl⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.true_geometry_final_vector_alt W hW u a ha hat row col hc κ hκ y hy hyU i x hx g hg
  rw [GlobalTheory.T.symmetricLevelCharacter_eq_addChar_superdiagSum (a.G i).S x _ h1 h2, _root_.GlobalTheory.T.true_geometry_final_volume_alt W hW u a ha hat row col hc κ hκ y hy hyU i g hg]
end GlobalTheory.FamTraceChiCol
end
end
end
end
