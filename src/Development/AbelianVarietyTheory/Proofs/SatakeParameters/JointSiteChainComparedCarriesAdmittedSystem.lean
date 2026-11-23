module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFramesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtMStatement
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLawAndFixedCoordinateStabiliserLawStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStepStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesIndependentAwayFromPlaceOverP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleJointDictionaryStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddingsStatement
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
public import Formalism.LocalToGlobal.InertKernelTheory.TieSerPin
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TieStabKaAtAny
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesPositiveSteps

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepDel

theorem del_of_pos : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPo hL j _ hj
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPo hL j hj

end GlobalTheory.TwV.StepDel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesPositiveStepsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_frameValues_positive_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  first | exact @GlobalTheory.TwV.StepDel.del_of_pos | exact GlobalTheory.TwV.StepDel.del_of_pos | (intros; apply GlobalTheory.TwV.StepDel.del_of_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesStepZero

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepZero

theorem del_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPos hL
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPos hL 0 (by have := GlobalTheory.TwU.m_eq t μ; omega)

end GlobalTheory.TwV.StepZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesStepZeroStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_frameValues_step_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  first | exact @GlobalTheory.TwV.StepZero.del_zero | exact GlobalTheory.TwV.StepZero.del_zero | (intros; apply GlobalTheory.TwV.StepZero.del_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesIndependentAwayFromPlaceOverPStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_series_independent_away_from_place_over_p : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Away) := by
  first | exact @GlobalTheory.TwV.away_of_dict | exact GlobalTheory.TwV.away_of_dict | (intros; apply GlobalTheory.TwV.away_of_dict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdAtServed

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

theorem std_at_served : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → 2 * rG L.sc ≤ D.R.k → ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Y.Fl u w hg).t (Y.Fl u w hg).mm (Y.Fl u w hg).c (D.gat u w hg).P.r ((Y.Fl u w hg).TT v) ((Y.Fl u w hg).a v) ((Y.Fl u w hg).b v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) := by
  intro D u w hg L hT X Y hLT hk v
  obtain ⟨hmm, -, -, hr, -⟩ := hLT u w hg
  have hS := (D.gat u w hg).P.setting v
  have hgk := hT.gat_k u w hg
  have hrG : 1 ≤ rG L.sc := Nat.succ_le_succ (Nat.zero_le _)
  have hm2 := D.R.two_le_m
  refine ⟨hg.1, hg.2.1, hS.two_le, hS.even, ?_, ?_, ?_, (Y.Fl u w hg).base v, (D.gat u w hg).P.dom v, ?_, ?_⟩
  · rw [hr]; split_ifs <;> omega
  · rw [hr, hgk]; split_ifs <;> omega
  · rw [hmm]; omega
  · exact fun s => ⟨le_trans (le_max_left _ _) ((Y.Fl u w hg).w_ge v s),
      le_trans (le_max_right _ _) ((Y.Fl u w hg).w_ge v s)⟩
  · exact fun s l hl _ => (Y.Fl u w hg).w_mono v s l hl

end GlobalTheory.TwU
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelSeries

section

@[expose] public section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

theorem eFac_ne_zero {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_) <;>
  · refine Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ ?_
    have hs := X.G.P.setting v
    haveI := hs.frac_alt
    have h1 : ((p : ℕ) : X.G.P.W v) ≠ 0 := hs.p_unif.ne_zero
    have h2 : ((p : ℕ) : X.G.P.Qq v) ≠ 0 := by
      rw [← map_natCast (algebraMap (X.G.P.W v) (X.G.P.Qq v))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr h1
    rw [← map_natCast (X.G.P.ι v)]
    exact (map_ne_zero _).mpr h2

theorem series_compatibility_of : TieSerOf := by
  intro p _ X Y j La _ c' L' _
  unfold srOf
  rw [smul_smul, inv_mul_cancel₀ (eFac_ne_zero Y j La (c', L')), one_smul]

end Formalism.L2.KerInert.SecondKernelSeries
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointSiteChainComparedCarriesAdmittedSystem

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV



private theorem admissible_at_each_site : Lt.AdmAtEnt2 → AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => DV.Used D μ → OrbitPlaces.Stab0 D → admitted D (sysS H X std) S.Y) := by
  intro hA D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hU hS0
  have hDict := GlobalTheory.T.latticeTuple_joint_dictionary t std J
  have hPair := GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hDict
  have hPos := GlobalTheory.T.site_place_induces_position_embeddings S
  have hMove := GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames S hDict
  have hAway := GlobalTheory.T.kernelSite_series_independent_away_from_place_over_p S hDict
  have hScal := GlobalTheory.T.kernelSite_seriesScalar_pow_integral S hDict
  have hK1 := GlobalTheory.T.allSites_k1_of_dict_pair_pos_scal S hDict hPair hPos hScal
  obtain ⟨hLaw, hLawIn, hXi⟩ := GlobalTheory.T.kernelSite_law_and_fixedCoordinateStabiliserLaw S hPair hPos hMove hAway
  obtain ⟨ι, hι⟩ := GlobalTheory.ThLoc.place_extends_to_iso _ S.lam
  haveI := Lt.fracAt Gl u w hg
  have key := hA D L hT Gi Gl Kc Dx cX ex t u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (kaAt X H hT) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg))
    (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT))
    (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le)
    S.E S.hfin S.hst S.g S.hLT
    (hT.gat_pos u w hg) ex.tw I (Formalism.L2.PairingIndexBounds.F.lev0At J.Gd u w hg) J.a ∅ t.cc t.δ t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
  have k2 := key S.curve hK1 hXi hLawIn
  refine k2 ⟨ι.toRingHom, Formalism.L2.KerInert.SecondKernelProjection.rdJ I X.onCh ι.toRingHom, Formalism.L2.KerInert.SecondKernelSeries.srOf S.Y, fun j hj => ⟨J.sharp j hj, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := tieStab_kaAtAny X H hT (chainAt H hT) (chainMu_cmp_K _) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y hU hS0 j hj.le
    rw [kaAtAny_cls] at h1
    rw [kaAt_cls]
    exact h1
  · refine Formalism.L2.KerInert.SecondKernelProjection.series_reading_entries D L hT Gi Gl Kc Dx cX ex u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds hT (chainMu_cmp_K _) X.onCh std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y ι.toRingHom ?_ j
    intro r
    have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
      rw [mem_algebraicClosure_iff]
      exact (Algebra.IsAlgebraic.isAlgebraic r).algHom D.what₂.embLL.toRatAlgHom
    show ι (D.what₂.embLL r) = S.E.iK (ex.cmp.embW u w hg r)
    rw [S.hK r hz, ← hι]
  · exact Formalism.L2.KerInert.SecondKernelSeries.series_compatibility_of (D.what₂.places.resChar w) _ S.Y j
  · have hD : S.Del j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        exact GlobalTheory.T.kernelSite_frameValues_step_zero S hDict hPair hPos hLaw
      · exact GlobalTheory.T.kernelSite_frameValues_positive_steps S hDict hPair hPos hLaw j hpos hj
    obtain ⟨cK, hn, hd⟩ := hD ι.toRingHom (fun z => hι z)
    refine ⟨cK, ?_, ?_, ?_, hd⟩
    · show ‖cK‖ ≤ 1
      rw [hn]
    · show ‖cK⁻¹‖ ≤ 1
      rw [norm_inv, hn, inv_one]
    · intro h
      rw [h, norm_zero] at hn
      exact zero_ne_one hn

theorem site_cmpLite_siteAdm : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}, Joint t H X → DV.Used D μ → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg (chainAt H hT) ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) Lv (chainAt H hT) := by
  intro hAdm hCur D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X J hU hS hk
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  refine ⟨⟨(kaAt X H hT).cmp, (kaAt X H hT).cmp_zero, (kaAt X H hT).cmp_K, (kaAt X H hT).rat, (kaAt X H hT).val⟩, ?_⟩
  have std : Lt.StdAtW D Gl u w hg := GlobalTheory.TwU.std_at_served D u w hg L hT Gi Gl J.tied hk
  obtain ⟨S⟩ := GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty hCur t std J
  have hA : admitted D (sysS H X std) S.Y := admissible_at_each_site hAdm S hU hS
  refine ⟨inferInstance, std, vpOf (D.gat u w hg), vpOf_irreducible (D.gat u w hg),
    eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    Lt.dGT D u (D.what₂.places.resChar w), Lt.dGT_spec (kaAt X H hT), _, S.Y, hA, Lt.dGT_zero _ _ _, fun j => ?_⟩
  unfold Lt.dGT
  split_ifs <;> simp

end GlobalTheory.TwV

end
end
end
