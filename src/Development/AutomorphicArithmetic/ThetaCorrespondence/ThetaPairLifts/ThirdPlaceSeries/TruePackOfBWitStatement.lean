module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColsStdOfBWit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.Divisibility.TupUsed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealAtColsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAtOfBWitStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.PkOf

section Heq

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7}

theorem mu_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.μ = S1.μ := by
  subst h
  cases eq_of_heq hS
  rfl

end Heq

theorem natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 E) ∈ PP.asIdeal) : (n : 𝓞 E) ∉ PP.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 E))
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hp)

theorem exists_of_mem_QE {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {PP : HeightOneSpectrum (𝓞 X.E)} (h : PP ∈ Formalism.L2.Col.QE sel ξ) : ∃ v, PP = sel v := by
  classical
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨v, rfl⟩
  · simp at h

end GlobalTheory.Fam.PkOf

namespace GlobalTheory.Fam

end GlobalTheory.Fam

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkHypOfReal

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PkOf
section Heq
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7}
end Heq
end GlobalTheory.Fam.PkOf
namespace GlobalTheory.Fam
theorem pkHyp_of_real_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin W.R W.S W.Q) → (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) → GlobalTheory.MiS.DcPtG W.P → _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx W.Q → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation W.Q → _root_.Formalism.IndefR.IndefiniteRealisationExtends W.Q → _root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q → W.Q.Rl.toRealDat.ExAt → Formalism.IndefR.Links.PrimRows3 W.Q.Rl W.Q.F → W.P.A3.fam3.TypesSep3 → (∃ s, W.P.A3.fam3.Ok3 s) → GlobalTheory.Core.Mi.IdE W.S.X → GlobalTheory.Count.GapGe W.S.X.B (100 * (B.R.r : ℝ) ^ 4) → Formalism.L2.SG.PackageTie2.FinX W.S.Y → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap (I.rec7 l Z) → _root_.GlobalTheory.Fam.ValidRealPackage W → _root_.GlobalTheory.Fam.GeometricFamilyConditions W → _root_.GlobalTheory.Fam.PackageHypotheses W := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hJ hLM hDc hFr hPins hSee hRec hEx hPrim hTS hOk3 hIdE hGap hFinX hNG hTW hTQ
  have hC3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hEx
  have hU : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 _ (W.P.I.tup t) := by
    apply Formalism.L2.DIV.tupAllUsed_of_cover
    intro t
    have hmu : W.Q.Rl.mu = W.P.S0.μ :=
      GlobalTheory.Fam.PkOf.mu_of_heq (congrArg (fun Z => W.P.A3.side3 W.P.P0 W.P.ψ0 Z) W.Q.zs) W.Q.s0
    rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨(I.rec7 l Z).plEq.symm w, ?_⟩
      show t = W.P.S0.μ ((I.rec7 l Z).plEq ((I.rec7 l Z).plEq.symm w))
      rw [← hmu, Equiv.apply_symm_apply]
      exact h.symm
  refine ⟨⟨⟨hJ, hLM, hDc, hC3, W.Q.frames hFr⟩, hPins, hSee, hU, hIdE, hGap, hFinX⟩, ?lev, hEx, hRec.hTop, hNG, ?fin, ?sel, ?aa⟩
  case lev =>
    obtain ⟨s, hs⟩ := hOk3
    have hR := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hs hTS W.Q.charW hPrim
    exact ⟨⟨s, hs⟩, hR.ratZ, _, hR.gUnit, hR.gEquiv, hR.h2P, hR.lev0, hR.lev1⟩
  case fin =>
    classical
    have h1 := W.Q.charW.tup.mu_off
    have h2 := W.Q.charW.tup.mu_used
    have : (Set.univ : Set W.P.T) ⊆ insert W.P.A3.A.μ0 (W.Q.Rl.mu '' (W.Q.Rl.twPl : Set _)) := fun t _ => by
      rcases h2 t with h | ⟨w, rfl⟩
      · exact Or.inl h
      · by_cases hw : w ∈ W.Q.Rl.twPl
        · exact Or.inr ⟨w, hw, rfl⟩
        · exact Or.inl (h1 w hw)
    exact Set.finite_univ_iff.1 ((((W.Q.Rl.twPl).finite_toSet.image _).insert _).subset this)
  case sel =>
    rintro PP PP' ⟨t, ht⟩ ⟨t', ht'⟩ hu
    have hs := hTW.ok.sel_ok
    obtain ⟨v, rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t PP).1 ht)
    obtain ⟨v', rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t' PP').1 ht')
    have e1 := congrArg HeightOneSpectrum.asIdeal hu
    have hv : v = v' := by
      apply HeightOneSpectrum.ext
      rw [← hs v, ← hs v']
      exact e1
    rw [hv]
  case aa =>
    intro PP h hmem
    have hcop := (I.rec7 l Z).host.ccK_coprime
    rcases h with ⟨t, ht⟩ | hg | ⟨u, hu⟩
    · apply hPins.qGuard.2 t PP ht
      push_cast
      exact Ideal.mul_mem_left _ _ hmem
    · obtain ⟨plg, iso, -, -, -, -⟩ := hPins.grpRecPin
      set kv := plg.symm ⟨PP, hg⟩ with hkv
      have hPP : ((plg kv : W.Q.Rl.toRealDat.Pg) : Pl (I.rec7 l Z).host.E) = PP := by
        rw [hkv, Equiv.apply_symm_apply]
      have h0 : (((I.rec7 l Z).host.g kv.1 : ℕ) : kP (plg kv).1) = 0 := by
        rw [← map_natCast (iso kv), ZMod.natCast_self, map_zero]
      have hg' : (((I.rec7 l Z).host.g kv.1 : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rw [← hPP]
        exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using h0)
      exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).host.g_level kv.1])) hg' hmem
    · exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).T_level u])) hu hmem
end GlobalTheory.Fam
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePackOfBWit

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem truePack_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → _root_.GlobalTheory.Fam.BundlePointConditions b → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  intro hL p K q c b hW hX hR
  obtain ⟨hOk, hPins, hTw, hStdC, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  obtain ⟨hChr, hXi, hQ, hLev, hRec, hRP, hOk3, hIdE, hLM⟩ := _root_.GlobalTheory.T.characters_match_bundle_alt q b hW
  have hTop := _root_.GlobalTheory.T.exists_read_at_packB_of_bWit q b hW hX
  have hTW : _root_.GlobalTheory.Fam.ValidRealPackage (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hOk, hPins, hTw, hStdC, hChr, ⟨1, hTop⟩⟩
  have hTQ : _root_.GlobalTheory.Fam.GeometricFamilyConditions (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hXi, hQ, hTop⟩
  obtain ⟨hRec'⟩ := hRec
  have hPk : _root_.GlobalTheory.Fam.PackageHypotheses (_root_.GlobalTheory.Fam.packB_alt b) := _root_.GlobalTheory.Fam.pkHyp_of_real_alt (_root_.GlobalTheory.Fam.packB_alt b) hR.join hLM hR.dc hR.frames hRP hR.see hRec' hR.ex hR.prim.1 hR.prim.2
    hOk3 hIdE hR.gapS hR.fin hR.gap hTW hTQ
  exact _root_.GlobalTheory.Fam.TruePackAlt.mk _ ⟨hPk, hTW, hTQ, hTS, hLev, ⟨hRec'⟩⟩
end GlobalTheory.Fam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePackOfBWitStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_pack_of_bundle_witness : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → _root_.GlobalTheory.Fam.BundlePointConditions b → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  first | exact @_root_.GlobalTheory.Fam.truePack_of_bWit_alt | exact _root_.GlobalTheory.Fam.truePack_of_bWit_alt | (intros; apply _root_.GlobalTheory.Fam.truePack_of_bWit_alt <;> assumption)
end
end
end
