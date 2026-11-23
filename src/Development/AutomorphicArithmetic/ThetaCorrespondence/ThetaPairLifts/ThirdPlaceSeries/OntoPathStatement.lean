module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodLiftOntoOfBase
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPart

section

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
open GlobalTheory.CharRealise

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)



theorem iw_split_eq (j : Fin D.R.m) (t : p.P.A3.fam3.base3.Tup) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw j t w = (S2 p).Iw j t w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw j t w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem d_split_eq : (p.S false).D = (S2 p).D := by
  show ((p.R.toCx3 p.F).data p.F.cr false).D = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem onWith_of_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), ∀ (C CH : ℝ) (err : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ), ONwith (S2 p) ((R2 p).num (F2 p) C CH) err → ONwith (p.S false) (p.N C CH) err ∧ (p.S false).D = (S2 p).D := by
  intro D L hT Gi Gl Kc Y cX ex Csz p C CH err h
  obtain ⟨h1, h2, h3⟩ := h
  have eD := d_split_eq p
  refine ⟨⟨fun w hw => ?_, fun w hw j => h2 w hw j, fun j => h3 j⟩, eD⟩
  have := h1 w hw
  simp only [iw_split_eq p, eD]
  exact this

end GlobalTheory.BigOn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPartStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.onClauses_with_error_of_splitPart : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), ∀ (C CH : ℝ) (err : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ), ONwith (S2 p) ((R2 p).num (F2 p) C CH) err → ONwith (p.S false) (p.N C CH) err ∧ (p.S false).D = (S2 p).D := by
  first | exact @GlobalTheory.BigOn.onWith_of_split | exact GlobalTheory.BigOn.onWith_of_split | (intros; apply GlobalTheory.BigOn.onWith_of_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnOfOnWithCanonical

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree

namespace GlobalTheory.BigOn

theorem canonical_error_real {ι J : Type} [Fintype J] (T : Finset ι) (I F err err0 J0 : ι → J → ℝ)
    (e c l : ι → ℝ) (D E E' : ℝ) (hD : 0 < D) (he : ∀ w, 0 < e w) (hl : ∀ w, 0 ≤ l w) (hE : 2 * E ≤ E')
    (hJ : ∀ w ∈ T, ∀ j, 0 ≤ J0 w j)
    (h0 : ∀ w j, err0 w j =
      max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) / (e w * (Fintype.card J : ℝ)))
    (h1 : ∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err w j) + c w) * D)
    (h2 : ∀ w ∈ T, ∀ j, 0 ≤ err w j)
    (h3 : ∀ j, ∑ w ∈ T, l w * (e w * err w j + e w * J0 w j) ≤ E) :
    (∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err0 w j) + c w) * D) ∧
    (∀ w ∈ T, ∀ j, 0 ≤ err0 w j) ∧
    ∀ j, ∑ w ∈ T, l w * (e w * err0 w j + e w * J0 w j) ≤ E' := by
  refine ⟨fun w hw => ?_, fun w _ j => ?_, fun j => ?_⟩
  · rcases isEmpty_or_nonempty J with hJe | hJn
    · simpa using h1 w hw
    · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
      have hew := he w
      have hs : ∑ j, e w * err0 w j =
          max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        simp only [h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      rw [Finset.sum_add_distrib, hs, ← div_le_iff₀ hD]
      have := le_max_right 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w)
      linarith
  · rw [h0]
    exact div_nonneg (le_max_left _ _) (mul_nonneg (he w).le (Nat.cast_nonneg _))
  · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩)
    have hA : ∀ w ∈ T, (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) ≤ ∑ j', l w * (e w * err w j') := by
      intro w hw
      have hew := he w
      have hs : (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) =
          l w * max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        rw [h0]; field_simp
      rw [hs, ← Finset.mul_sum _ _ (l w)]
      refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (hl w)
      · exact Finset.sum_nonneg fun j' _ => mul_nonneg hew.le (h2 w hw j')
      · have h := h1 w hw
        rw [Finset.sum_add_distrib, ← div_le_iff₀ hD] at h
        linarith
    have hB : ∀ j', ∑ w ∈ T, l w * (e w * err w j') ≤ E := fun j' =>
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg (he w).le (hJ w hw j'))) (hl w)) (h3 j')
    have hC : ∑ w ∈ T, l w * (e w * J0 w j) ≤ E :=
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (he w).le (h2 w hw j))) (hl w)) (h3 j)
    have hF : (Fintype.card J : ℝ) * ∑ w ∈ T, l w * (e w * err0 w j) ≤ (Fintype.card J : ℝ) * E := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum hA) ?_
      rw [Finset.sum_comm]
      refine le_trans (Finset.sum_le_sum fun j' _ => hB j') ?_
      simp
    have hG := le_of_mul_le_mul_left hF hn
    simp only [mul_add, Finset.sum_add_distrib]
    linarith

theorem on_of_onWith_canonical :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (Z : IndefScale Bs) (C C' CH CH' : ℝ) (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ), 0 < S.D → 0 ≤ Z.E1u → 2 * C ≤ C' → (∀ w ∈ S.Tw, ∀ j, 0 ≤ Z.J0 (S.μ w) w j) → (∀ w j, S.err0 w j = max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) - ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * Z.F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) / ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))) → ONwith S (Z.num C CH) err → S.ON (Z.num C' CH') := by
  intro K _ _ _ Bs Df S Z C C' CH CH' err hD hE hC hJ h0 h
  rw [on_iff_with]
  obtain ⟨h1, h2, h3⟩ := h
  exact canonical_error_real S.Tw
    (fun w j => (S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ)) Z.F0 err S.err0
    (fun w j => Z.J0 (S.μ w) w j) (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ))
    (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) (fun w => Formalism.DivisionValues.lw w) (S.D : ℝ)
    (C * Z.E1u) (C' * Z.E1u) (by exact_mod_cast hD) (fun w => ramw_pos w) (fun w => (lw_pos w).le)
    (by nlinarith [mul_le_mul_of_nonneg_right hC hE]) hJ h0 h1 h2 h3

end GlobalTheory.BigOn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChain

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnAtPlacesBase

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

theorem on_of_has_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : HasIndexBound O) (hD : LeafData O) (hJ : GlobalTheory.TraceClassRank.RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : HasTwistBound O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hE : HasExpBound N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ∃ err, ONwith S N err := by
  obtain ⟨Th1, a, r1, r2, de2, hT0⟩ := hT0
  obtain ⟨ε, h1⟩ := h1
  obtain ⟨-, Jp, hJS, hJE⟩ := hE
  exact ⟨_, GlobalTheory.TraceClassRank.on_core_atPlaces N
    ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2, ε0 := ε, Jp := Jp } : OnObj S P c) CE hRk
    hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1⟩

end Free

theorem on_base_atPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hO s N C hOk h1 h2 hM hμ hth hU hB hrat hRk hSq hY hSup hSp hS hT0
    hD hJ hI hT2 hT1 hSh hBS hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1
  classical
  obtain ⟨hc, hinj, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  have hN : TieLevelNum O (rankPred D.R) D.R.f := by
    letI := st
    letI := hostAlg D
    refine ⟨hd.f_eq, ?_⟩
    rw [hO.rr_eq, OntoChain.rank_eq]
    push_cast
    rfl
  obtain ⟨w, hw⟩ := GlobalTheory.BigOnBase.exists_tieCoord_base ht (fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩) hOk h1 h2 hM.HV hM.jV hM.HW hμ (phasedLift_one hth) hU hB hrat hI hT2
  obtain ⟨tU, hMk, hP⟩ := level_of_tied ht hOk.irr h1
  exact on_of_has_atPlaces N (withCoord O w) C hRk hMk hSup hP hw hSp hS hT0 hD hJ hI hT2 hT1 hSh
    (leafIndexU_of O D.R.f (mirab_levelGroups _ _) hSq hY tU hN) hBS (leafUnip_of O D.R.f (mirab_levelGroups _ _) hSq tU hN)
    hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1

end GlobalTheory.OnAtPlacesBase

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChainStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedPlacesBoundChain_twoRunChain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  first | exact @GlobalTheory.OnAtPlacesBase.on_base_atPlaces | exact GlobalTheory.OnAtPlacesBase.on_base_atPlaces | (intros; apply GlobalTheory.OnAtPlacesBase.on_base_atPlaces <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoPath

section

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn.OntoPath
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem onto_path_alt : _root_.GlobalTheory.BigOn.TwoRunsStatement → _root_.GlobalTheory.BigOn.RationalityStatement' → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → _root_.GlobalTheory.BigOn.TwistStatement' →
    _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hRuns hRat hGeo hRank hTw hSh hBad hExp hPage
  have H := ((((((((hRuns.and hRat).and hGeo).and hRank).and hTw).and hSh).and hBad).and hExp).and hPage)
  refine Closed.imp H ?_
  intro eps Fm CH _ H _
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨xR, hR⟩, ⟨xQ, hQ⟩⟩, ⟨cG, hG⟩⟩, ⟨cK, hK⟩⟩, ⟨cT, hT⟩⟩, ⟨cS, hS⟩⟩, ⟨cB, hB⟩⟩, ⟨cE, hE⟩⟩, ⟨cP, hP⟩⟩ := H
  set c0 : ℝ := max (max (max (max cG cK) (max cT cS)) (max (max cB cE) cP)) 1 with hc0
  let c : OnConst := ⟨c0, 14, 66 * c0 + 4⟩
  have hcb : OnPage.ConstBad c := ⟨le_rfl, le_rfl⟩
  have l1 : cG ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l2 : cK ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l3 : cT ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l4 : cS ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l5 : cB ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l6 : cE ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l7 : cP ≤ c.C := le_trans (by simp) (le_max_left _ _)
  obtain ⟨x1, h1⟩ := hG c l1 hcb
  obtain ⟨x2, h2⟩ := hK c l2 hcb
  obtain ⟨x3, h3⟩ := hT c l3 hcb
  obtain ⟨x4, h4⟩ := hS c l4 hcb
  obtain ⟨x5, h5⟩ := hB c l5 hcb
  obtain ⟨x6, h6⟩ := hE c l6 hcb
  obtain ⟨x7, h7⟩ := hP c l7 hcb
  refine ⟨2 * max c.CE 0, by positivity,
    max (max (max xR xQ) (max x1 x2)) (max (max x3 x4) (max (max x5 x6) x7)), ?_⟩
  intro x hx hx0 i p hp hm C hCC
  have a0 : max xR xQ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx0)
  have b0 : max x1 x2 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx0)
  have c1 : max x3 x4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx0)
  have d0 : max (max x5 x6) x7 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx0)
  obtain ⟨r, hr, hown⟩ := hR x hx (le_trans (le_max_left _ _) a0) i p hp hm
  have hrat := hQ x hx (le_trans (le_max_right _ _) a0) i p hp hm
  have hct := hm.2.1
  obtain ⟨O, hO⟩ := exists_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ (Fm.parT x hx i) (Fm.ex x hx i).kap_def
    (Fm.ex x hx i).errX r c hct.canon hct.halfEX hr
  have hrec : RecAt p (Fm.parT x hx i) r O := ⟨hO, hown⟩
  obtain ⟨gSup, gSpan, gLem, gData, gIdx, gDepth⟩ := h1 x hx (le_trans (le_max_left _ _) b0) i p hp hm r O hrec
  have kRank := h2 x hx (le_trans (le_max_right _ _) b0) i p hp hm r O hrec
  have tTw := h3 x hx (le_trans (le_max_left _ _) c1) i p hp hm r O hrec
  have sSh := h4 x hx (le_trans (le_max_right _ _) c1) i p hp hm r O hrec
  have bBad := h5 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  have eExp := h6 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  obtain ⟨pPage, pSizes, pX, pBad, pLev, pY, -, pE1u, pTie⟩ :=
    h7 x hx (le_trans (le_max_right _ _) d0) i p hp hm r O hrec
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hm.1
  obtain ⟨hC, hOk, hU, hBL, hRR, -⟩ := hL
  have hI := GlobalTheory.ClassSumIdentity.leafIdentity_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hrat
  have hT2 := GlobalTheory.BaseTwistIncl.leafTW2_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hBL hrat
  obtain ⟨dG, dR, d2, dL⟩ := gDepth c.CE CH
  obtain ⟨err, herr⟩ := GlobalTheory.T.twistedPlacesBoundChain_twoRunChain _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1
    ((R2 p).num (F2 p) c.CE CH) c.CE hOk hC.grp.levels hC.grp.chiW hC.models hC.tup.mu_conj hC.thP.thG hU hBL hrat hRR
    pLev pY gSup gSpan gLem gIdx gData kRank hI hT2 tTw sSh bBad dG dR d2 dL pPage pSizes pX pBad (eExp c.CE CH) le_rfl
    (pTie c.CE CH)
  obtain ⟨hon, hD⟩ := GlobalTheory.T.onClauses_with_error_of_splitPart _ _ _ _ _ _ _ _ _ _ p c.CE CH err herr
  have hDpos : 0 < (p.S false).D := by rw [hD]; exact hRR.1
  have hJ : ∀ w ∈ (p.S false).Tw, ∀ j, 0 ≤ p.Z.J0 ((p.S false).μ w) w j := (eExp C CH).1
  exact on_of_onWith_canonical _ _ _ (p.S false) p.Z c.CE C CH CH err hDpos pE1u
    (le_trans (mul_le_mul_of_nonneg_left (le_max_left c.CE 0) zero_le_two) hCC) hJ (fun w j => p.err_eq w j) hon
end GlobalTheory.BigOn.OntoPath
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoPathStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.onto_x_of_all_estimates : _root_.GlobalTheory.BigOn.TwoRunsStatement → _root_.GlobalTheory.BigOn.RationalityStatement' → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → _root_.GlobalTheory.BigOn.TwistStatement' → _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  first | exact @_root_.GlobalTheory.BigOn.OntoPath.onto_path_alt | exact _root_.GlobalTheory.BigOn.OntoPath.onto_path_alt | (intros; apply _root_.GlobalTheory.BigOn.OntoPath.onto_path_alt <;> assumption)
end
end
end
