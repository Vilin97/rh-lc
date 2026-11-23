module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCountTh
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumShift
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbVal
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ScalKindPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThSomePf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhase
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCountSteps

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.FCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eligible_totally_positive {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : EligPos u u' F0 what₂ :=
  fun γ w h => Formalism.L2.SG.WConst.atPt_totPos γ w h.2

end Formalism.L2.SG.Pf.FCount
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumTop

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB

variable {D : Formalism.BasicNotions.D7}

theorem orbCut_all {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : OrbCut M a c := by
  haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  exact Formalism.L2.SG.Pf.LocOrbCut.orbitDecomposition_of_integrand M hOK a c (Formalism.L2.SG.Pf.LocOrbCut.val M hOK a c)

theorem localOrbitSum_holds (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (hA : ∀ p, Agree δ M p) :
    LocOrbSum M δ u u' :=
  locOrbSum_of M δ u u' (fun p w => modShift_holds δ _ _ p w)
    (fun p a c => orbCut_all (M p) (hA p).1 a c)
    (fun p => nAutNe_of M p (hA p).1)

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThRestrPf

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Restr2

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem thRestricted_of (hA : ∀ p, Agree δ M p) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hRel : PCount.EligRel u u' F0 what₂) :
    ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) := by
  intro γ w h
  have hZ : PCount.AtMat w (zT γ) := PCount.atMat_zT hN hrows h (hRel γ w h)

  have hpt : ptT γ = w := by
    have h0 := h
    obtain ⟨⟨hgen, -⟩, hat⟩ := h
    obtain ⟨y, hy⟩ := hN γ w hat (hRel γ w h0) hgen
    have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
        PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
    have hn : nrep γ = some hex.choose := dif_pos hex
    obtain ⟨hRep, -, hL, hU, e⟩ := hex.choose_spec
    obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
    have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
      hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
    unfold ptT
    rw [hn]
    exact hw.symm
  have hfin := PCount.tupZ_restr hA u u' hZ
    ((LocModel.good_cofinite δ M hA ∅).mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (fun x => LocModel.LM.iotaIntegral_almost_all D x)
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine (hfin.union hall).subset fun p hp => ?_
  by_contra hq
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hq
  obtain ⟨htup, hg⟩ := hq
  have hg' : Good δ M w p := hg
  apply hp
  show thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ)) = _
  rw [hpt]
  have hmem : CntLocal.ZZP (M := M) δ u u' p (zT γ) * LsDatumB.sgnP p ∈ x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [← htup]
    exact ⟨1, 1, one_intLow p, one_intUp p, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  obtain ⟨l, ρ, hl, hρ, he⟩ := hmem
  have hZZ : CntLocal.ZZP (M := M) δ u u' p (zT γ) =
      l * modMat δ (D.mem u).A.T (D.mem u').A.T p w * ρ * LsDatumB.sgnP p := by
    rw [← he, Matrix.mul_assoc, permSign_mul_self₂, Matrix.mul_one]
  have e2 : CntLocal.ZZP (M := M) δ u u' p (zT γ) + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := by
    rw [hZZ, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, loU_corner p _ ⟨hl.1, hl.2.1⟩ ⟨hρ.1, hρ.2.1⟩,
      corner_sgn]
  unfold thL
  apply clsOf_triv
  have e3 : (CntLocal.ZZP (M := M) δ u u' p (zT γ) + Matrix.of fun a b =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ (D.mem u).A.T (D.mem u').A.T p w else 0) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := e2
  rw [e3]
  refine isGL_mul _ (isGL_mul _ (isGL_mul _ (isGL_of_det_one _ hl.2.2 (det_loU ⟨hl.1, hl.2.1⟩))
    (shift_isGL _ _ w p (hA p) hg')) (isGL_of_det_one _ hρ.2.2 (det_upU ⟨hρ.1, hρ.2.1⟩))) (isGL_sgn p)

end Restr2

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

theorem thRestricted_holds_of {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hN : Formalism.L2.SG.PairVal.NormRepExists D u u' F0 what₂)
    (hRel : PCount.EligRel u u' F0 what₂) :
    Formalism.L2.SG.LsDatumB.ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) :=
  LocUnramB.thRestricted_of hA hrows hN hRel

end Formalism.L2.SG.Pf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThSomeClose

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem thSome_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hNR : NormRepElig u u' F0 what₂) :
    ThSome M δ u u' F0 what₂ := by
  refine thSome_holds_of hA hNR fun γ w hγ p a b => ?_
  obtain ⟨Λ, hΛ, F', hF'⟩ := dnInDens_of hNR hrows γ w hγ
  exact PI.CntNotIntW.integral_on_pairs_holds D δ M hA u u' hT F0 what₂ hrows Λ hΛ (zT γ) F' hF' p a b

end Formalism.L2.SG.Pf
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiProdE

section

@[expose] public section

noncomputable section

theorem psi_product_e : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.SG.Pf.Coef.PsiProdE D := fun D x =>
  (product_formula_e D.host.F D.host.E _ D.sp.cm.deg2 (fun p => D.s.atP p)).2 x

end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutAt

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_leaves {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hM : Formalism.L2.SG.Pf.NormRepMove D u u')
    (hPG : PhaseLocG M δ u u' F0 what₂) (hVP : VolIdxProd M δ u u' F0 what₂)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩)
    (hFS : FCount.FibSum M δ u u' F0 what₂) (hDT : FCount.DensTh M δ L u u') :
    CutAt M δ L u u' F0 what₂ := by
  have hNR := normRepElig_of hN
  have hU := Formalism.L2.SG.Pf.locUnram_holds hA u u'
  have hR := Formalism.L2.SG.Pf.thRestricted_holds_of hA hrows hN PCount.eligRel_holds
  have hTS := Formalism.L2.SG.Pf.thSome_holds hA hc hrows hNR
  refine ⟨LocOrbSumPf.localOrbitSum_holds M δ u u' hA, Formalism.L2.SG.Pf.scalKind_of hrows,
    coefficient_product_of_local hA hc hrows hN hM (phaseLoc_of hA hPG) (psi_product_e D) hVP,
    Formalism.L2.SG.Pf.partnerCount_holds hA hc hrows hP hU hR hE hS hG hI hτ hT,
    FCount.fiberCount_of_rest hA hc hP hU hR hrows hN PCount.eligRel_holds (hE ⟨hc, hrows, hP⟩) hTS hFS
      nu_not_class_holds hDT (FCount.eligible_totally_positive u u' F0 what₂),
    hNR, hTS, ⟨LocModel.thTriv M, hU, hR⟩⟩

end Formalism.L2.SG.Pf.Coef
end
end
end
