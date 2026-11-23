module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbeddingAtLocalFactor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymDataOfUnifCongr
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffUpMemStdHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfGRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiStdEqConstMulLocXi
import Formalism.LocalToGlobal.Columns.AdelicLemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairIdentity

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel



namespace GlobalTheory.Fam.TopLoc

theorem locTop_eq_of_type : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S S' : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S')
   (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (P : Formalism.L2.Col.rowSG Pr sel mu) (P' : Formalism.L2.Col.rowSG Pr sel mu'),
   P.1 = P'.1 → P.1 ∈ Pr.vGs → cst.sharp = cst'.sharp →
   (∀ a, Formalism.L2.Col.IntAt P.1 a → cst.psi P (a / (Formalism.L2.Col.qOf P.1 : X.E)) = Formalism.L2.Col.psi0P Ch P.1 (Formalism.L2.Col.redP P.1 a)) →
   (∀ a, Formalism.L2.Col.IntAt P'.1 a → cst'.psi P' (a / (Formalism.L2.Col.qOf P'.1 : X.E)) = Formalism.L2.Col.psi0P Ch P'.1 (Formalism.L2.Col.redP P'.1 a)) →
   ∀ m2 y y', (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) * y' i)) →
     GlobalTheory.TopStep.locTop Ch sel mu cst m2 P y y' = GlobalTheory.TopStep.locTop Ch sel mu' cst' m2 P' y y' := by
  intro X Pr R Ch sel S S' mu mu' cst cst' P P' hPP hmem hsh hpsi hpsi' m2 y y' hy
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold GlobalTheory.TopStep.locTop Formalism.L2.Col.PhiTop Formalism.L2.Col.ftY
  rw [if_pos hmem, if_pos hmem', hsh, if_pos hmem, if_pos hmem', ← hPP]
  congr 1
  split_ifs with hη
  · set η := Formalism.L2.Col.atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hηdef
    have hq : ((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    have hsum : η ((Formalism.L2.Col.qOf P.1 : X.E) • y') = ∑ i, ((Formalism.L2.Col.qOf P.1 : X.E) * y' i) * η (Pi.single i 1) := by

      conv_lhs => rw [pi_eq_sum_univ' ((Formalism.L2.Col.qOf P.1 : X.E) • y'), map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    have hε : Formalism.L2.Col.IntAt P.1 (Formalism.L2.Col.epsSg : X.E) := by
      simpa [Formalism.L2.Col.epsSg] using Formalism.L2.Col.IntAt.coe P.1 (-1)
    have hint : Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.epsSg : X.E) * η ((Formalism.L2.Col.qOf P.1 : X.E) • y')) := by
      refine hε.mul ?_
      rw [hsum]
      exact GlobalTheory.TopStep.intAt_sum _ fun i _ => (hy i).mul (hη i)
    have hb : (Formalism.L2.Col.epsSg : X.E) * η y' = (Formalism.L2.Col.epsSg : X.E) * η ((Formalism.L2.Col.qOf P.1 : X.E) • y') / (Formalism.L2.Col.qOf P.1 : X.E) := by
      rw [map_smul, smul_eq_mul]; field_simp
    have e1 := hpsi _ hint
    have e2 := hpsi' _ (hPP ▸ hint)
    rw [← hPP] at e2
    rw [hb, e1, e2]
  · rfl

section Normal
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SymChain GlobalTheory.SymChain.UnifChange GlobalTheory.Fam.MidLoc

theorem exists_normal_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (ϖ' : kˣ) (h : valuation k ((ϖ' : k) - (S.ϖ : k)) < valuation k (S.ϖ : k)) (τ : ℕ) :
    ∃ S' : SymData k s κ, S'.ϖ = ϖ' ∧ S'.ψ = S.ψ ∧ (∀ j, j ≤ s + 2 → S'.μ j = S.μ j) ∧
      (∀ j, s + 2 < j → S'.μ j = 1) ∧ (S'.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop := by
  let S₁ : SymData k s κ :=
    { S with ϖ := ϖ', unif := isUnif_of_near S.unif h, sym := isSymLevel_of_near S.cond S.unif h S.sym }
  have hTop : (S₁.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop :=
    transport_iterPhi S.P S.μ S.tame (s + 1) (near_refl _) (near_typeFrame h _)
  let μ : ℕ → kˣ →* ℂˣ := fun j => if j ≤ s + 2 then S₁.μ j else 1
  have ht : ∀ j, IsTame (μ j) := fun j => by
    simp only [μ]
    split_ifs
    · exact S₁.tame j
    · exact fun _ _ => rfl
  have e : ∀ j, 1 ≤ j → j ≤ s + 2 → μ j = S₁.μ j := fun j _ hj => if_pos hj
  exact ⟨withMu S₁ μ ht, rfl, rfl, fun j hj => if_pos hj, fun j hj => if_neg (by omega),
    (withMu_le S₁ μ ht e (Fin τ)).2.1.trans hTop⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

end Normal

end GlobalTheory.Fam.TopLoc
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsLocFacXiStd

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel

noncomputable section
namespace GlobalTheory.Fam.TopLocFac
theorem isLocFac_xiStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ n : Fin a.n,
   GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg ((a.G n).s + 1)) (_root_.GlobalTheory.Fam.TopLoc.standardXi a n) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ht n
  have hid := ((ha.tie (fun t => (nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g ht.pinX.std t).some) fun t => (nonempty_colCh (D := I.rec7 l Z) u _).some).2.idem n).1
  obtain ⟨hs, hX, -⟩ := hW.tr.ok.spaces
  have hsd : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L := fun j hj => by
    have e : ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ :=
      Set.ext (ht.pinX.xs j hj).2.2
    have h1 := GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq ((I.rec7 l Z).sp.X j) hs _ (hX j)
    have h2 : GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j) = (a.g.x j).L := SetLike.coe_injective (h1.trans e.symm)
    rw [← h2]
    exact GlobalTheory.PlaceModel.isSelfDualC_latFrame _
  have hm : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, (a.G n).FX ((a.G n).s + 1) le_rfl, (a.G n).FM, _,
    (GlobalTheory.QTw.GeoInhab.int_dense (a.G n).q hid).2, hid,
    GlobalTheory.StdHomAt.int_iff_up_mem_stdHom _ _ (a.G n).q (a.G n).unit _ _ _ _ _ _ _ _ (hsd _ (by omega)) (hsd _ hm.le)
      (ht.pinX.xs _ (by omega)).2.2 (ht.pinX.xs _ hm.le).2.2 ((a.G n).latX _ _) (a.G n).latM,
    GlobalTheory.LastTwoSteps.xiTop_mem_SB _ (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) (a.G n).S.cond (a.G n).unitVol (by simp) _,
    (a.G n).cg_top, fun _ => rfl⟩
end GlobalTheory.Fam.TopLocFac
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAtTypeTop

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel

namespace GlobalTheory.Fam.TopLoc
section Normal
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SymChain GlobalTheory.SymChain.UnifChange GlobalTheory.Fam.MidLoc
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
theorem exists_atType_with_same_psi_and_phi_max (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (hϖ : valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) :
    ∃ S' : SymData (a.G n).k (a.G n).s B.R.k, S'.ψ = (a.G n).S.ψ ∧ (S'.T (Fin B.R.t)).PhiTop = ((a.G n).S.T (Fin B.R.t)).PhiTop ∧
      ∀ (b : I.ι) (P : BadPr I b), P.1 = (a.pl n).1 →
        AtType I.Ch I.sel (I.tup b) (I.cst b) B.embLL P (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) S' := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain ⟨hid, hv⟩ := hR.idem n
  obtain ⟨hi, hd⟩ := SymChainAt.place_facts (a.G n).q hid
  have hPm : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
  obtain ⟨i, g1, g2, -, g4, -⟩ := LevelData.type_prime hPm
  obtain ⟨ϖ, hϖq, -⟩ := LevelData.exists_unif (ι := (a.G n).q.pr.comp (incA (I.rec7 l Z))) hi hd (g1 ▸ g4)
  obtain ⟨S', e1, e2, e3, e4, e5⟩ := exists_normal_top (a.G n).S ϖ
    (by rw [hϖq, map_natCast, Valuation.map_sub_swap]; exact hϖ) B.R.t
  refine ⟨S', e2, e5, fun b P hP => ?_⟩
  obtain ⟨PP, hPP⟩ := P
  obtain rfl : PP = (a.pl n).1 := hP
  have ok := hW.tr.ok
  have hok := ok.idx_ok b
  have f1 : Formalism.L2.Col.psi0P I.Ch (a.pl n).1 = I.Ch.psi0 ⟨_, hPm⟩ := dif_pos hPm
  have f2 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 = Formalism.L2.Col.chiAt I.Ch ⟨_, hPm⟩ := dif_pos hPm
  refine ⟨hPm, hs.symm, hok.cst_ok, ok.sharp _, by rw [hW.tr.tw.cst_eq]; exact Nat.le_succ _,
    fun x hx => hok.psi0 ⟨_, hPP⟩ x hPm hx, ⟨hi, hd, rfl, e1 ▸ hϖq⟩, fun x hx => ?_, fun j x v h1 h2 h3 => ?_⟩
  · rw [e2]
    exact psi_tie (a.G n).q hv hi hd (g1 ▸ g2) (g1 ▸ g4) (hok.xiUnitAtPrime ⟨_, hPP⟩).1 (_root_.GlobalTheory.Fam.pk_z W).ψ W.Q.stdChar B.embLL _
      (fun z c h => f1 ▸ ok.weil ⟨_, hPm⟩ z c h) _ (a.G n).char x hx
  · rw [Formalism.L2.Col.LocE.unitV, dif_pos h2]
    by_cases hj : j < B.R.m
    · rw [e3 _ (by omega)]
      have key := chi_tie (a.G n).q hid hi hd (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta (j + 1)
        (c := (Units.map (B.embLL : B.fields.K →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch (a.pl n).1 j)) (hW.tr.chr ⟨j, hj⟩)
        (fun y x c hx hy => Units.ext (by
          have h := hok.mu0G ⟨j, hj⟩ ⟨_, hPm⟩ x y c hx hy
          have e3 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = I.Ch.chi ⟨j, hj⟩ ⟨_, hPm⟩ := (congrFun f2 j).trans (dif_pos hj)
          rw [e3]
          exact h.symm))
        W.Q.charW.base.lev.eta
        (fun y x c hx hy => ((_root_.GlobalTheory.Fam.pk_z W).C.isEta.unr (a.pl n).1 _ (by
          have hy' : y ∉ (a.pl n).1.asIdeal := fun h => by
            haveI := (a.pl n).1.isPrime
            exact c.ne_zero (hy.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
          change Valued.v (((x : (I.rec7 l Z).host.E)) : (a.pl n).1.adicCompletion (I.rec7 l Z).host.E) = 1
          rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hx]
          exact ((a.pl n).1.valuation_eq_one_iff_notMem (K := (I.rec7 l Z).host.E)).2 hy')).symm)
        _ (hR.mu n (j + 1) (by omega) hj) x v h2.unit h1 rfl h3
      rw [key]
      rfl
    · rw [e4 _ (by omega), ((congrFun f2 j).trans (dif_neg hj) : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = 1)]
      simp
end Normal
theorem loc_top_common_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 1 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hiA n j hj hjm
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s + 1 := by omega
  have hR := (hIs.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g hTr.pinX.std t).some)
    fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2
  obtain ⟨S', hψ, hΦ, hAt⟩ := _root_.GlobalTheory.Fam.TopLoc.exists_atType_with_same_psi_and_phi_max hW a hR n (_root_.GlobalTheory.LevUnif.unif_of_gRead_alt W hW u a _ _ hR n)
  have hxi : ∀ yb, (S'.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) S'.ψ (a.G n).ν (-1) yb =
      ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) yb := fun yb => by
    unfold Chain.xiTop
    rw [hΦ, hψ]
    rfl
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1)))
      (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((a.G n).s + 1)) (Fin B.R.t) ((a.G n).s + 2) ⊕ Unit ≃ Fin (B.R.N B.R.m)),
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e →
      ∀ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ (y : Formalism.L2.Col.HomE B.fields.E (B.R.N ((a.G n).s + 1)) (B.R.N B.R.m)) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
       (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) * y' i)) →
       ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
           (Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y' (e' r))) (GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' y) =
         C * B.embLL (GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P y y') := by
    by_cases h0 : ∃ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1
    · obtain ⟨t₀, P₀, hP₀⟩ := h0
      have hA₀ := hAt _ P₀ hP₀
      obtain ⟨e'₀, he'₀⟩ := GlobalTheory.QTw.exists_xOrd B.R ((a.G n).s + 1)
      obtain ⟨e₀, he₀⟩ := GlobalTheory.QTw.exists_topOrd B.R (a.G n).s hs
      obtain ⟨C, hC0, hC⟩ := (GlobalTheory.SymBridge.matchAtType _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol hA₀).2.2 e'₀
        (e₀.trans (finCongr (congrArg B.R.N hs))) he'₀ (fun r => he₀ r)
      refine ⟨C, hC0, fun e' e he' he t P hP y y' hy => ?_⟩
      obtain rfl : e' = e'₀ := Equiv.ext fun r => Fin.ext ((he' r).trans (he'₀ r).symm)
      obtain rfl : e = e₀.trans (finCongr (congrArg B.R.N hs)) := Equiv.ext fun r => Fin.ext ((he r).trans (he₀ r).symm)
      have hA := hAt _ P hP
      have hPP : P₀.1 = P.1 := hP₀.trans hP.symm
      have hy₀ : ∀ i, Formalism.L2.Col.IntAt P₀.1 ((Formalism.L2.Col.qOf P₀.1 : B.fields.E) * y' i) := by rw [hPP]; exact hy
      refine ((congrFun (hxi _) _).symm.trans (hC y y' hy₀)).trans ?_
      exact congrArg (fun x => C * B.embLL x)
        (locTop_eq_of_type I.Ch I.sel _ _ _ _ P₀ P hPP hA₀.mem (hA₀.sharp.trans hA.sharp.symm) hA₀.psi0 hA.psi0 _ y y' hy₀)
    · exact ⟨1, one_ne_zero, fun _ _ _ _ t P hP => absurd ⟨t, P, hP⟩ h0⟩
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ => ⟨_root_.GlobalTheory.Fam.TopLoc.standardXi a n, _root_.GlobalTheory.Fam.TopLocFac.isLocFac_xiStd_alt W hW u a hIs hTr n, fun P hP z => ?_⟩⟩
  rw [_root_.GlobalTheory.Fam.TopFrames.xiStd_eq_const_mul_locXi_alt W hW u a hIs hTr hiA n t J hJ α γ P hP C (fun e' e he' he y y' hy => hC e' e he' he t P hP y y' hy) hj z,
    ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
end GlobalTheory.Fam.TopLoc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAtTypeTopStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_row_pair_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 1 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  first | exact @_root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt | exact _root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt | (intros; apply _root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt <;> assumption)
end
end
end
