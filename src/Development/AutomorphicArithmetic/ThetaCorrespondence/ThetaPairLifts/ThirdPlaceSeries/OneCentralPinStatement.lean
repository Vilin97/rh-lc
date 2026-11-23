module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecSingleAt
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.QuotientMetricDivisors.Statement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineOfGlued
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTupStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtension
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StabMatchStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchesDifferCentralStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchingCosetStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralBottomDatum

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem GlobalTheory.MiTop.levChi_mul_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  unfold Lev.levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg _ ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

theorem GlobalTheory.MiTop.conj_in_level {G : Type} [Group G] (J : Subgroup G) (χ : G → ℂ)
    (hm : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (h0 : ∀ a, χ a ≠ 0) {k : G} (hk : k ∈ J) (j : G) :
    (j ∈ J ↔ k * j * k⁻¹ ∈ J) ∧ (j ∈ J → χ (k * j * k⁻¹) = χ j) := by
  refine ⟨⟨fun hj => J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk), fun hj => ?_⟩, fun hj => ?_⟩
  · have := J.mul_mem (J.mul_mem (J.inv_mem hk) hj) hk
    rwa [show k⁻¹ * (k * j * k⁻¹) * k = j by group] at this
  · have e := hm _ (J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk)) _ hk
    rw [show k * j * k⁻¹ * k = k * j by group, hm _ hk _ hj, mul_comm (χ k)] at e
    exact (mul_right_cancel₀ (h0 k) e).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPoints

section

@[expose] public section

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem oneBlock_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : LevDat D.host.E ℂ V.rank)
    (hn : V.rank ≤ Λ.r) (hs : Λ.s = 0) (hQ : Λ.Q = ∅) (κ : GA D V) :
    (κ ∈ levS V β Λ ↔ κ ∈ GfC V ∧ Lev.finE V κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) β ∧
      Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ) ∈ Λ.P.H) ∧
    Lev.levChi V β Λ κ = ((Formalism.L2.DIV.ext1 Λ.P.H Λ.P.chi
      (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ)) : ℂˣ) : ℂ) := by
  refine ⟨⟨fun h => ?_, fun h => ⟨h.1, ?_⟩⟩, ?_⟩
  · have hl := mem_lev.1 h.2
    exact ⟨h.1, (mem_parLev.1 hl.1).2.1, hl.2⟩
  · refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, h.2.1,
      fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _, fun PP hPP => ?_⟩, h.2.2⟩
    rw [hQ] at hPP
    exact absurd hPP (Finset.notMem_empty _)
  · unfold Lev.levChi levFn
    simp only [hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]


end GlobalTheory.MiTop

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtensionStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.central_adapted_element_value_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | exact _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | (intros; apply _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsAt

section

@[expose] public section



section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop

theorem exists_isAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hP hF
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.Core.Mi.PinModel.exists_transport_adelic_correction (W.S.tr u)
  obtain ⟨a, haf, hac, hSt⟩ := _root_.GlobalTheory.T.exists_central_stab_of_transport_correction W hW u f B hP hF a₀ ha₀
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hC := _root_.GlobalTheory.T.central_adapted_element_value_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hb : (show GA D (D.sp.Y 0) from f.g.b 0) ∈ GfC (D.sp.Y 0) := by
    obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, hv, ht, -⟩ := hP
    have h1 := hv.b 0
    rw [ht.b 0] at h1
    exact h1
  have hx : (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) ∈ GfC (D.sp.Y 0) :=
    (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq _).1 (by simp)
  have htf : _root_.GlobalTheory.MiTop.translationElement f B a₀ a ∈ GfC (D.sp.Y 0) :=
    mul_mem (mul_mem (inv_mem hx) (GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o (mul_mem ha₀.1 haf))) hb
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    rw [rank_eq W.S.X W.Q.instEq, W.S.X.n_eq]
  refine ⟨a₀, a, ha₀, haf, hac, htf, fun κ => ?_⟩
  rw [inv_inv]
  have h1 := GlobalTheory.FrameConj.levS_conj_frame (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) htf κ
  generalize _root_.GlobalTheory.MiTop.translationElement f B a₀ a * κ * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹ = y at h1 ⊢
  obtain ⟨h2, h3⟩ := oneBlock_lev (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) hn rfl rfl y
  have h4 : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ y ∈ levS (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) := h1.1
  have h5 : Lev.levChi (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) y = _root_.GlobalTheory.MiTop.realCharacter W κ := h1.2
  rw [h2] at h4
  refine ⟨h4.trans ⟨fun h => (hM y h.1 h.2.1).2 h.2.2, fun h => ?_⟩, fun hk => ?_⟩
  · obtain ⟨hf, hs⟩ := (hSt y).2 ⟨h.1, h.2.1⟩
    exact ⟨hf, hs, (hM y hf hs).1 h⟩
  · obtain ⟨hf, hs, hp⟩ := h4.1 hk
    exact (hC y hf hs hp ((hM y hf hs).2 hp)).trans (h3.symm.trans h5)
end GlobalTheory.MiTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsAtStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.exists_isAt_of_placed_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a := by
  first | exact @_root_.GlobalTheory.MiTop.exists_isAt_alt | exact _root_.GlobalTheory.MiTop.exists_isAt_alt | (intros; apply _root_.GlobalTheory.MiTop.exists_isAt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneCentralPin

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
theorem GlobalTheory.MiTop.matches_mul_of_mem_rJ' {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    {t k : GA D (D.sp.Y 0)} (ht : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t) (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (t * k) := by
  refine ⟨mul_mem ht.1 hk.1, fun j => ?_⟩
  have hc := GlobalTheory.MiTop.conj_in_level (G := GA D (D.sp.Y 0))
    (Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (_root_.GlobalTheory.MiTop.realCharacter W)
    (fun a ha b hb => GlobalTheory.MiTop.levChi_mul_lev _ _ _ ha hb) (fun a => Lev.levChi_ne_zero _ _) hk j
  have h2 := ht.2 (k * j * k⁻¹)
  have e : (t⁻¹)⁻¹ * (k * j * k⁻¹) * t⁻¹ = ((t * k)⁻¹)⁻¹ * j * (t * k)⁻¹ := by group
  rw [e] at h2
  exact ⟨hc.1.trans h2.1, fun hj => (h2.2 (hc.1.1 hj)).trans (hc.2 hj)⟩
theorem GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → GlobalTheory.MiTop.Framed B → ∃ d : _root_.GlobalTheory.MiTop.BottomData W u, d.B = B ∧ d.b = (show GA D (D.sp.Y 0) from f.g.b 0) ∧ d.Pin z := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr
  classical
  by_cases hex : ∃ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B ∧ Framed B
  · obtain ⟨u₀, f₀, B₀, hpl₀, hF₀⟩ := hex
    obtain ⟨a₀, a, hAt⟩ := _root_.GlobalTheory.T.exists_isAt_of_placed_framed W hP u₀ f₀ B₀ (by first | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed _ _ hpl₀ | exact hpl₀) hF₀
    have hm := _root_.GlobalTheory.MiTop.botHyp_match_alt W hP.bot
    have hS : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
      have h1 := hm.2.2.2.1 1 (one_mem _) (one_mem _)
      rwa [one_mul] at h1
    obtain ⟨z, hzf, hzc, c, hcf, hcc, k₀, hk₀, ht⟩ :=
      _root_.GlobalTheory.T.matching_translates_bottom_alt W hP.bot hr u₀ B₀ _ hAt.2.2.2.1 _ hS.1 hAt.2.2.2 hS
    have ht₀ : _root_.GlobalTheory.MiTop.translationElement f₀ B₀ a₀ (c⁻¹ * a) = z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ := by
      have hc : a₀ * (c⁻¹ * a) = c⁻¹ * (a₀ * a) := by
        rw [← mul_assoc, Subgroup.mem_center_iff.1 (inv_mem hcc) a₀, mul_assoc]
      unfold _root_.GlobalTheory.MiTop.translationElement at ht ⊢
      rw [hc, map_mul, map_inv]
      generalize (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u₀) = x at ht ⊢
      generalize embA B₀.d B₀.o (a₀ * a) = p at ht ⊢
      generalize embA B₀.d B₀.o c = q at ht ⊢
      generalize (show GA D (D.sp.Y 0) from f₀.g.b 0) = b at ht ⊢
      generalize (show GA D (D.sp.Y 0) from W.Q.tS) = s at ht ⊢
      calc x⁻¹ * (q⁻¹ * p) * b = x⁻¹ * q⁻¹ * x * (x⁻¹ * p * b) := by group
        _ = z * s * k₀ := by rw [ht]; group
    have hAt₀ : _root_.GlobalTheory.MiTop.IsTranslate' f₀ B₀ a₀ (c⁻¹ * a) := by
      refine ⟨hAt.1, mul_mem (inv_mem hcf) hAt.2.1, mul_mem (inv_mem hcc) hAt.2.2.1, ?_⟩
      rw [ht₀]
      exact _root_.GlobalTheory.MiTop.matches_mul_of_mem_rJ' W (hm.2.2.2.1 z hzf hzc) hk₀
    refine ⟨z, hzf, hzc, fun u f B hpl hF => ?_⟩
    obtain ⟨b₀, b, hAt'⟩ := _root_.GlobalTheory.T.exists_isAt_of_placed_framed W hP u f B (by first | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed _ _ hpl | exact hpl) hF
    obtain ⟨a₁, hAt1, k, hk, hkt⟩ := _root_.GlobalTheory.T.placed_bessel_compatibility_alt W hP hr u u₀ f f₀ B B₀ hpl hpl₀ hF hF₀ b₀ b a₀ _ hAt' hAt₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBT, _⟩ := hpl
    refine ⟨⟨B, (show GA D (D.sp.Y 0) from f.g.b 0), b₀, a₁, k₀ * k⟩, rfl, rfl,
      ⟨hBT.adapted, hAt1.1, hAt1.2.1, hAt1.2.2.1, ?_, ?_⟩⟩
    · exact (Formalism.IndefR.Lev.levG _ _ _).mul_mem hk₀ hk
    · have e := hkt
      rw [ht₀] at e
      unfold _root_.GlobalTheory.MiTop.translationElement at e
      show embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0) =
        (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * (k₀ * k))
      have e' : ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
          (embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0)) =
          z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ * k := by
        rw [← mul_assoc]; exact e
      rw [← mul_assoc (z * _) k₀ k, ← e', mul_inv_cancel_left]
  · exact ⟨1, one_mem _, one_mem _, fun u f B hpl hF => (hex ⟨u, f, B, hpl, hF⟩).elim⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneCentralPinStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.exists_botDat_of_placedP_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → GlobalTheory.MiTop.Framed B → ∃ d : _root_.GlobalTheory.MiTop.BottomData W u, d.B = B ∧ d.b = (show GA D (D.sp.Y 0) from f.g.b 0) ∧ d.Pin z := by
  first | exact @_root_.GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed | exact _root_.GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed | (intros; apply _root_.GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed <;> assumption)
end
end
end
