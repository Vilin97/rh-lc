module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDetStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevelStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDense

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SymBridge.ComplDense

theorem small_in_prime_and_dense : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) ∧ ∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1 := by
  intro E _ _ k _ _ _ _ PP q ι ϖ h hu
  refine ⟨fun z hz => (GlobalTheory.SymBridge.ComplRes.mem_P_iff h hu z).mpr hz, fun y hy => ?_⟩
  obtain ⟨i, -, hv⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep_one h hu y ((Valuation.mem_integer_iff _ _).mp hy)
  refine ⟨(i : 𝓞 E), ?_⟩
  have e : ι (((i : ℕ) : 𝓞 E) : E) = (i : k) := by simp
  rw [e]
  exact lt_of_le_of_lt hv (GlobalTheory.SymBridge.ComplRes.v_unif_lt_one hu)

end GlobalTheory.SymBridge.ComplDense
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDenseStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.completion_smallIntegers_in_prime_dense : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) ∧ ∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1 := by
  first | exact @GlobalTheory.SymBridge.ComplDense.small_in_prime_and_dense | exact GlobalTheory.SymBridge.ComplDense.small_in_prime_and_dense | (intros; apply GlobalTheory.SymBridge.ComplDense.small_in_prime_and_dense <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrix

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

theorem GlobalTheory.LocRed.red_entry_movedFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  intro D k _ _ _ _ q PP hPP ϖ _ V β Λ N _ Y _ _ F σ b hb g gk hg hSt a a' z hz
  have hM : (mt V g).map q.pr * F.β.submatrix id σ = F.β.submatrix id σ * gk.val.submatrix σ σ := by
    have h1 : (mt V g).map q.pr = F.β * gk.val * F.γ := hg.2
    have hs : ∀ A : Matrix (Fin V.rank) (Fin V.rank) k, A * F.β.submatrix id σ = (A * F.β).submatrix id σ := fun A => by
      ext i j; simp [Matrix.mul_apply]
    rw [h1, Matrix.submatrix_mul_equiv F.β gk.val id σ σ, hs, Matrix.mul_assoc (F.β * gk.val), F.γβ, Matrix.mul_one]
  have key := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β b g _ _ hb hM hSt a a' z hz.symm
  simpa [Matrix.submatrix_apply] using key

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrixStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  first | exact @GlobalTheory.LocRed.red_entry_movedFrame | exact GlobalTheory.LocRed.red_entry_movedFrame | (intros; apply GlobalTheory.LocRed.red_entry_movedFrame <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtPlace

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
noncomputable section
namespace GlobalTheory.QLevMid

theorem level_at_place_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t PP hP E hRes j d hd hj x hxK
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.pk.bot.hyp.2.2.2.1.lev
  obtain ⟨N, hSD⟩ : ∃ N, IsSDFrame (Yc _ j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) N := ⟨_, hl.βY j hj⟩
  have hPg : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg,
      PP'.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ≠
        PP.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := by
    intro PP' hPP' e
    have hApart := GlobalTheory.StepLifts.places_apart _ hl t
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with hEq | hConj
    · exact Finset.disjoint_left.1 hApart.2 hPP' (hEq ▸ hP)
    · exact hApart.1 PP' hPP' PP (Or.inr hP) (GlobalTheory.GoodPrimes.isConjPl_iff.2 hConj)
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frame j d hd
  have hloc := (a.Q PP ⟨t, hP⟩).gl_loc j d hd x
  obtain ⟨hG, hSt, hOff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  have hRed := GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ (a.Q PP ⟨t, hP⟩).compl _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  obtain ⟨hι, hrep⟩ := GlobalTheory.T.completion_smallIntegers_in_prime_dense _ _ PP _ _ _ (a.Q PP ⟨t, hP⟩).compl (a.Q PP ⟨t, hP⟩).unif
  have hSt' := hSt.2 hxK
  have hQ : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, PP'.under (𝓞 (I.rec7 l Z).host.F) = PP.under (𝓞 (I.rec7 l Z).host.F) → PP' = PP :=
    fun PP' hP' h => hW.pk.sel PP' PP ⟨t, hP'⟩ ⟨t, hP⟩ h
  obtain ⟨hmem, hchi⟩ := GlobalTheory.T.mem_twistPlaceLevel_single_place_character _ _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) (I.rec7 l Z).R.r (I.rec7 l Z).R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) PP hP hPg hQ _ hG hOff
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hC1 := GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel _ _ PP _ hι (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η _ e he x hxK _ (hRed hSt')
  have hC2 := GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet _ _ PP _ hι hrep (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) hRes _ e he x
  rw [← hr] at hC1 hC2
  refine ⟨hmem.trans ⟨fun h => hC1.1 h.2, fun h => ⟨hSt', hC1.2 h⟩⟩, fun hx => ?_⟩
  exact (hchi hSt').trans (congrArg Units.val (hC2 hx _ (hRed hSt') (hC1.2 hx)))
end GlobalTheory.QLevMid
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtPlaceStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_twist_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  exact @_root_.GlobalTheory.QLevMid.level_at_place_alt_alt
end
end
end
