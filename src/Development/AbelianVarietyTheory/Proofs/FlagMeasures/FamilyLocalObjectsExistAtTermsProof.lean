module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseDataOfGlobalTermStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermLiesOverLocalDatumAfterIsometry
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeToStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitRepsOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFiniteStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermsSameDoubleCosetSameLocalDataStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataGlobalTermIndependentOfRepresentativeStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRowsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermLiesOverLocalDatumAfterIsometryStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.globalTerm_lies_over_localDatum_after_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → ∃ d, Over P d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  first | exact @GlobalTheory.LocOver.GlobOver.over_local | exact GlobalTheory.LocOver.GlobOver.over_local | (intros; apply GlobalTheory.LocOver.GlobOver.over_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRowSameWeightSameLocalData

section

@[expose] public section

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.TermSame

theorem same : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' ∧ (nmlOf Y u u' t = nmlOf Y u u' t' → ∀ (p : PlF D) (P : LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), P.RelG (LocNG.theta (Y.M p)) → ∀ d, Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) → Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.toTerm.lam (lf D (X.Fu u)) (Quot.out t'.toTerm.cls).1 (Tu D u) (Tu D u'))) := by
  intro D X Y u u' t t' hG hr
  have hl : t.lam = t'.lam := congrArg (fun r => (r.1 : {Λ // Λ ∈ Y.what₂ u}).1) hr
  have hl' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : {Λ // Λ ∈ Y.what₂ u'}).1) hr
  have hi : iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := congrArg (fun r => r.2.2) hr
  refine ⟨by simp only [Formalism.L2.SG.TermOp.wt, hl, hl'], fun hnml p P hP d hO => ?_⟩
  have hΛ : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hΛ' : IsRowLat D (X.Fu u) t'.lam := (Y.rowsOK u).1 t'.lam t'.mem
  have one_nrat : ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F := by
    intro T F
    have h := one_mem_NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) F
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hnml]
    exact ⟨1, one_nrat _, 1, one_nrat _, by simp⟩
  obtain ⟨n, hn, n', hn', hlin⟩ := hmem
  have h0 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have h1 : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t'.rep.2.2.1
  have hmN : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := by
    have h := GlobalTheory.HL.CosetConst.conj_nlam_top (G := lf D (X.Fu u')) h0 hn'
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  have hβ : n * (t.lin * n' * t.lin⁻¹) = t'.lin * t.lin⁻¹ := by
    rw [hlin]; simp only [mul_assoc]
  have hgm : Formalism.HermitianLatticesTheory.gmap (n * (t.lin * n' * t.lin⁻¹)) t.lam = t.lam := by
    have hg0 : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    have hg1 : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam := t'.rep.2.2.2.1
    rw [hβ, Formalism.L2.SG.Pf.MainEqClass.gmap_mul', Formalism.L2.SG.Pf.MainEqClass.gmap_inv_of' hg0, hl', hg1, hl]
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    rw [hβ]
    show frame (mapLF t'.lin (lf D (X.Fu u'))) a = (t'.lin * t.lin⁻¹) (frame (mapLF t.lin (lf D (X.Fu u'))) a)
    rw [GlobalTheory.HL.CosetConst.frame_mapLF h1, GlobalTheory.HL.CosetConst.frame_mapLF h0]
    show _ = t'.lin (t.lin.symm (t.lin _))
    rw [LinearEquiv.symm_apply_apply]
  have hI := Formalism.L2.SG.Pf.iotaDict_fwd Y t t' hl hl' hi
  rw [← hβ] at hI
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1
  have hrel : DCRel t.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 t.frame :=
    (hEq (Quot.out t.toTerm.cls) ⟨t.frame, t.rep.2.2.2.2⟩).1 (Quot.out_eq _)
  have hR0 : Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 ≠ 0 := hG
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    have e : Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 = Gval (lf D (X.Fu u)) t.frame :=
      hGF (Quot.out t.toTerm.cls) ⟨t.frame, t.rep.2.2.2.2⟩ hrel
    rw [← e]; exact hR0
  have hGt' : Gval (lf D (X.Fu u)) t'.frame ≠ 0 := by
    have hh : t'.lin = n⁻¹⁻¹ * t.lin * n' := by rw [inv_inv]; exact hlin
    rw [← GlobalTheory.HL.CosetConst.G_eq_frames t t' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn) hn' hh]
    exact hGt
  have s1 := (GlobalTheory.T.localData_globalTerm_independent_of_representative D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t.lam hΛ
    (Quot.out t.toTerm.cls).1 t.frame (Quot.out t.toTerm.cls).2 t.rep.2.2.2.2 hR0 hrel p P hP d).1 hO
  have hpd' : PD D t.lam (lf D (X.Fu u)) u' t'.frame := by rw [hl]; exact t'.rep.2.2.2.2
  have s2 := GlobalTheory.T.global_terms_same_doubleCoset_same_local_data D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t.lam hΛ t.frame t'.frame
    t.rep.2.2.2.2 hpd' hGt n hn _ hmN hgm hfr hI p P hP d s1
  have s3 : Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.lam (lf D (X.Fu u)) t'.frame (Tu D u) (Tu D u')) := by
    rw [← hl]; exact s2
  have hEq' := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t'.lam hΛ'
  have hrel' : DCRel t'.lam (lf D (X.Fu u)) t'.frame (Quot.out t'.toTerm.cls).1 :=
    (hEq' ⟨t'.frame, t'.rep.2.2.2.2⟩ (Quot.out t'.toTerm.cls)).1 (Quot.out_eq _).symm
  exact (GlobalTheory.T.localData_globalTerm_independent_of_representative D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t'.lam hΛ' t'.frame
    (Quot.out t'.toTerm.cls).1 t'.rep.2.2.2.2 (Quot.out t'.toTerm.cls).2 hGt' hrel' p P hP d).1 s3

end GlobalTheory.LocOver.TermSame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRowSameWeightSameLocalDataStatement

section

@[expose] public section

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.terms_same_row_same_weight_same_localData : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' ∧ (nmlOf Y u u' t = nmlOf Y u u' t' → ∀ (p : PlF D) (P : LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), P.RelG (LocNG.theta (Y.M p)) → ∀ d, Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) → Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.toTerm.lam (lf D (X.Fu u)) (Quot.out t'.toTerm.cls).1 (Tu D u) (Tu D u'))) := by
  first | exact @GlobalTheory.LocOver.TermSame.same | exact GlobalTheory.LocOver.TermSame.same | (intros; apply GlobalTheory.LocOver.TermSame.same <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalObjectFamilyClassesDetermineRows

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs
open scoped Classical

namespace GlobalTheory.FamGen

open Formalism.MainNotions.S.Lat GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_clsLoc_self {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) {r : ℕ} (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Y0 ∈ clsLoc M Y0 := by
  have hI : IntUni M (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := by
    refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun a b => ?_⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  refine ⟨1, 1, hI, hI, fun a b => ?_, ?_⟩
  · rw [sub_self]; exact Submodule.zero_mem _
  · rw [Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]

theorem exists_famTie : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), (∀ t ∈ TS, t.G ≠ 0) → (∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') → ∀ t₀ ∈ TS, t₀.relevant → ∃ Fm : LocFam (zOf Y) Cl (NuC D), FamTie TS cls (nmlOf Y u u') (ptPN t₀) Fm ∧ (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) ∧ (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t) ∧ (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ c, 0 ≤ Fm.rw c) := by
  intro D X Y u u' Cl TS cls hG hrow t₀ ht₀ hrel
  obtain ⟨w, hw, hat, hfin⟩ := GlobalTheory.T.terms_at_point_of_relevant_term_relevant_finite D X Y u u' t₀ (hG t₀ ht₀) hrel
  have hRL : IsRowLat D (X.Fu u) t₀.toTerm.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  obtain ⟨-, hG0, hcell0⟩ := hat t₀ rfl
  obtain ⟨F00, F'0, F'1, FP, d0, hn, hZ, -, hcell1, hp, hfinP⟩ :=
    GlobalTheory.T.baseData_of_global_term D (zOf Y) u u' (X.Fu u) t₀.toTerm.lam hRL (Quot.out t₀.toTerm.cls).1
      (Quot.out t₀.toTerm.cls).2 hG0 w hcell0
  have hreps := fun p => GlobalTheory.LocOver.orbit_reps_over ((zOf Y).M p) ((zOf Y).agree p).1 (locH (zOf Y) p) D.R.rS (FP p)
  let R : ∀ p : PlF D, LocNG.Reps (FP p) := fun p => (hreps p).2.1.some
  let LT : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ∀ p : PlF D, Formalism.MainNotions.S.Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS :=
    fun s p => locU (zOf Y) p s.lam (lf D (X.Fu u)) (Quot.out s.cls).1 (Tu D u) (Tu D u')
  let rho : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ∀ p : PlF D, LocNG.Datum (FP p) :=
    fun s p => if h : ∃ d ∈ (R p).RD, Over (FP p) d (LT s p) then h.choose else d0 p

  have hover : ∀ t : TauC Y u u', ptPN t = ptPN t₀ → ∀ p, ∃ d, Over (FP p) d (LT t.toTerm p) := by
    intro t ht p
    obtain ⟨-, hGt, hct⟩ := hat t ht
    exact GlobalTheory.T.globalTerm_lies_over_localDatum_after_isometry D (zOf Y) u u' (X.Fu u) t.toTerm.lam ((Y.rowsOK u).1 t.lam t.mem) (Quot.out t.toTerm.cls).1
      (Quot.out t.toTerm.cls).2 hGt w F00 F'0 hct hZ p (FP p) (hp p).1
  have hrho : ∀ t : TauC Y u u', ptPN t = ptPN t₀ → ∀ p, rho t.toTerm p ∈ (R p).RD ∧ Over (FP p) (rho t.toTerm p) (LT t.toTerm p) := by
    intro t ht p
    obtain ⟨d, hd⟩ := hover t ht p
    obtain ⟨y, hy, hyd⟩ := (R p).hRD.2.1 d (Set.mem_univ _)
    have hex : ∃ d ∈ (R p).RD, Over (FP p) d (LT t.toTerm p) := ⟨y, hy, (hreps p).2.2 d y _ ((hreps p).1.symm hyd) hd⟩
    have e : rho t.toTerm p = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec

  let γ := ptPN t₀
  let Pf : Finset (PlF D) := hfinP.toFinset
  let Om : Finset {p // p ∈ Pf} := Pf.attach.filter (fun p => ¬ (FP p.1).PrimeTo)
  let Ds : ∀ p : PlF D, Finset (LocNG.Datum (FP p)) := fun p => hfin.toFinset.image (fun s => rho s p)
  have hmemDs : ∀ t : TauC Y u u', ptPN t = γ → ∀ p, rho t.toTerm p ∈ Ds p := fun t ht p =>
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨t, ht, rfl⟩)
  let dat : Cl → NuC D → Option (∀ p : {p // p ∈ Pf}, {d // d ∈ Ds p.1}) := fun c ν =>
    if h : ∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν then
      some (fun p => ⟨rho h.choose.toTerm p.1, hmemDs _ h.choose_spec.2.2.1 p.1⟩) else none
  let rw : Cl → ℝ := fun c => if h : ∃ t ∈ TS, cls t = c then (Formalism.L2.SG.TermOp.wt h.choose) ^ 2 else 0
  let ngenL : PlF D → ℝ := fun p => (ngenLoc (R p) (d0 p) (clsLoc ((zOf Y).M p)
    ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1)))).toReal
  let Fm0 : LocFam (zOf Y) Cl (NuC D) := ⟨Pf, Om, FP, R, d0, Ds, ngenL, 0, rw, dat⟩
  let Fm : LocFam (zOf Y) Cl (NuC D) := { Fm0 with V0 := if h : ∃ v, OrbitFamilyIdentityAt Fm0 v then h.choose else 0 }
  have hDs : ∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD := by
    intro p _ d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨t, ht, rfl⟩ := hfin.mem_toFinset.1 hs
    exact (hrho t ht p).1
  have hnotP : ∀ p, p ∉ Pf → (FP p).PrimeTo ∧ LocNG.IsTermOver (FP p) (d0 p) ⟨lattice₂ D (zOf Y).M p t₀.toTerm.lam,
      scaled (zOf Y) p (frame F00), scaled (zOf Y) p (frame F'0), ((Tu D u : ℕ) : (D.s.atP p).Fp),
      ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩ := by
    intro p hp'
    by_contra hc
    exact hp' (hfinP.mem_toFinset.2 hc)
  refine ⟨Fm, ⟨w, F00, F'0, F'1, hw, hDs, rfl, hn, hZ, fun p => (hp p).1, ?_, fun p hp' => (hnotP p hp').1, ?_,
    ⟨t₀, ht₀, rfl, fun p _ => (hp p).2.2.1⟩, fun p _ => ⟨_, (hp p).2.2.1⟩,
    ⟨t₀.toTerm.lam, hRL.1.1.toIsLattice, fun p hp' => (hnotP p hp').2⟩, ?_, hcell1, fun p _ => ⟨rfl, d0 p, _, (hp p).2.2.1, ?_⟩⟩,
    fun p _ => (hp p).2.1, fun p _ => ⟨d0 p, _, (hp p).2.2.1⟩, hDs, fun c => ?_⟩
  · intro p
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_attach _ _))
  · intro p hp' t _ ht
    obtain ⟨-, hGt, hct⟩ := hat t ht
    obtain ⟨d, g, hg, d', hdd', hto⟩ := GlobalTheory.T.globalTerm_lies_over_localDatum_after_isometry D (zOf Y) u u' (X.Fu u) t.toTerm.lam ((Y.rowsOK u).1 t.lam t.mem)
      (Quot.out t.toTerm.cls).1 (Quot.out t.toTerm.cls).2 hGt w F00 F'0 hct hZ p (FP p) (hp p).1
    have hpr := (hnotP p hp').1
    have hrel' : LocNG.Datum.Rel (d0 p) d' :=
      GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo ((zOf Y).M p) ((zOf Y).agree p).1 (locH (zOf Y) p) D.R.rS D.R.k (FP p) (rank_Vp p) (hp p).2.1 hpr
        (d0 p) d' _ _ (hp p).2.2.1 hto
    exact ⟨g, hg, d', hrel', hto⟩
  · intro c ν
    by_cases h : ∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν
    · have e : Fm.dat c ν = some (fun p => ⟨rho h.choose.toTerm p.1, hmemDs _ h.choose_spec.2.2.1 p.1⟩) := dif_pos h
      rw [e]
      obtain ⟨hc1, hc2, hc3, hc4⟩ := h.choose_spec
      refine ⟨h, fun t ht hct hpt hnt => ⟨fun p _ => ?_, ?_⟩⟩
      · have hsame := GlobalTheory.T.terms_same_row_same_weight_same_localData D X Y u u' h.choose t (hG _ hc1) (hrow _ hc1 t ht (hc2.trans hct.symm))
        obtain ⟨g, hg, d', hdd', hto⟩ := hsame.2 (hc4.trans hnt.symm) p (FP p) (hp p).2.1 _ (hrho _ hc3 p).2
        exact ⟨g, hg, d', hdd', hto⟩
      · have hc : ∃ t ∈ TS, cls t = c := ⟨t, ht, hct⟩
        have e2 : Fm.rw c = (Formalism.L2.SG.TermOp.wt hc.choose) ^ 2 := dif_pos hc
        rw [e2]
        obtain ⟨hh1, hh2⟩ := hc.choose_spec
        rw [(GlobalTheory.T.terms_same_row_same_weight_same_localData D X Y u u' hc.choose t (hG _ hh1) (hrow _ hh1 t ht (hh2.trans hct.symm))).1]
    · have e : Fm.dat c ν = none := dif_neg h
      rw [e]
      exact h
  · show (locH (zOf Y) p).Zhat (locU (zOf Y) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f
      (locU (zOf Y) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f' ∈ _
    have hm := mem_clsLoc_self ((zOf Y).M p) ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1))
    convert hm using 3
    all_goals first | rfl | exact (hp p).2.2.2
  · show 0 ≤ (if h : ∃ t ∈ TS, cls t = c then (Formalism.L2.SG.TermOp.wt h.choose) ^ 2 else 0)
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

end GlobalTheory.FamGen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalObjectFamilyClassesDetermineRowsStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs
open scoped Classical

theorem _root_.GlobalTheory.T.exists_localObjectFamily_classesDetermineRows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), (∀ t ∈ TS, t.G ≠ 0) → (∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') → ∀ t₀ ∈ TS, t₀.relevant → ∃ Fm : LocFam (zOf Y) Cl (NuC D), FamTie TS cls (nmlOf Y u u') (ptPN t₀) Fm ∧ (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) ∧ (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t) ∧ (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ c, 0 ≤ Fm.rw c) := by
  first | exact @GlobalTheory.FamGen.exists_famTie | exact GlobalTheory.FamGen.exists_famTie | (intros; apply GlobalTheory.FamGen.exists_famTie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem existFam : ExistFam := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hctx K S TS cls hF γ hP => ?_⟩
  have hTie : ConcTie X Y := hctx.2.2
  obtain ⟨hTS, _, hrow⟩ := hF
  obtain ⟨t₀, ht₀, hv, rfl⟩ := hP
  have hG : ∀ t ∈ TS, t.G ≠ 0 := by
    intro t ht h0
    rw [hTS] at ht
    apply ht.1
    show Gt t = 0
    simp [Gt, h0]
  have hrel : t₀.relevant := (GlobalTheory.T.nonGeneric_family_classes_determine_rows D X Y u u' hTie).2.2 t₀ hv
  exact GlobalTheory.T.exists_localObjectFamily_classesDetermineRows D X Y u u' TS cls hG hrow t₀ ht₀ hrel

end GlobalTheory.SnFam
end
end
end
