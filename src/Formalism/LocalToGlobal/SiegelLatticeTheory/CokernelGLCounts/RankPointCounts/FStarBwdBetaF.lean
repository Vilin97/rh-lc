module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdPairOfTermBeta
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowLatOfMove
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LastCoordMem
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBeta
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwd
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPartPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StarExists2OfGood

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdTermOfGx

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem bwdTerm'_of_gx (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of' (btOK_holds Zd) hGX

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdTermHolds

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem bwdTerm'_holds : BwdTerm' Zd u u' F0 what₂ := bwdTerm'_of_gx (genXiRev_holds Zd)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaRep

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem repG_holds : RepG u u' F0 what₂ := by
  intro hC γ Z hZ
  obtain ⟨w, hγ, -⟩ := hZ
  have hN := normRepExists_ctx hC
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hrep : repF γ = hex.choose.2.1 := by unfold repF; rw [hn]
  obtain ⟨⟨hPD, hmk⟩, -⟩ := hex.choose_spec
  refine ⟨⟨hex.choose.2.1, hPD⟩, hrep.symm, hmk, ?_⟩
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hrow
  have hrel := (hEq ⟨hex.choose.2.1, hPD⟩ (Quot.out γ.cls)).1 (hmk.trans (Quot.out_eq γ.cls).symm)
  have e := Formalism.L2.SG.Pf.g_value_function _ _ _ _ _ hrel
  exact fun h0 => hG (e.symm.trans h0)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNH

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coef_int (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame (lf D F0) a ∈ Λ₂) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame (lf D F0) a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) •
      (tLoc Zd p γ).f a := by

    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, baseChangeAt_frame_eq Zd p γ (hu p), Units.smul_def, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) • (tLoc Zd p γ).f a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (hu p (Fin.last D.R.rS)) (by rw [sgnP_last, frFac_last', mul_one])
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_y (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ₂ : Submodule.IsLattice D.host.E Λ₂) (hSD₂ : BwdNA.SD (VS D) Λ₂)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (hzX : F0.z ∉ Xsp (lf D F0)) :
    ∃ y ∈ Λ₂, y ∈ orth (VS D) (Xsp (lf D F0)) ∧ (VS D).hT y F0.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f F0.z)⁻¹ • f
  have hρz : ρ F0.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp (lf D F0), ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp (lf D F0)).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame (lf D F0) i.castSucc) = 0 := fun i => by
    rw [frame_cs]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame (lf D F0) (Fin.last D.R.rS)) = 1 := by
    have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [this, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame (lf D F0)))
  have hint : ∀ m ∈ Λ₂, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by

      rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_int Zd γ hprim hu c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂ hSD₂ U v hint
  have hw : ∀ a, (VS D).hT w (frame (lf D F0) a) = ρ (frame (lf D F0) a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame (lf D F0) a) w, ← h0, ← BwdNA.hsw (VS D) (frame (lf D F0) a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (F0.e i), ← frame_cs, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [← this, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdN

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdN_zorth : F0.z ∈ orth (VS D) (Xsp (lf D F0)) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F0.z x]
    have h := NMoveP.hT_f_X F0 (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem bwdN_znotX : F0.z ∉ Xsp (lf D F0) := by
  intro h
  have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 (bwdN_zorth (F0 := F0)) F0.z h
  rw [F0.z_norm, neg_eq_zero] at h0
  have hT := (D.mem u).A.T_prime.ne_zero
  exact hT (Nat.cast_eq_zero.1 h0)

variable (u u' F0 what₂)


theorem bwdN_holds : BwdN Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hmem₂
  obtain ⟨hΛ₂, hloc₂⟩ := hmem₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have ht1 := fun p => (hT2 p).1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    BwdNP.unit_of_frame Zd p γ (ht1 p).1.2.1 a
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (ht1 p).1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (ht1 p).1.2.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hLset : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f =
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => by
    have h := (hloc₂ p).2.1
    rw [hφ p] at h
    rw [← h]
    exact (Set.image_id _).symm
  have hSD := BwdNP.sd_of_loc Zd (Λ := γ.lam) inferInstance hSDl
  have hSD₂ := BwdNP.sd_of_loc Zd (Λ := Λ₂) inferInstance hSDl₂
  set X := Xsp (lf D F0) with hXdef
  have hXiso : ∀ x ∈ X, ∀ y ∈ X, (VS D).hT x y = 0 := fun x hx y hy => NMoveP.hT_X_X F0 hx hy
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) X) → w ∈ X := fun {w} hw =>
    BwdNA.mem_of_orth_orth (VS D) X fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXo := BwdNA.X_le_orth (VS D) X hXiso
  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) X → ∃ y ∈ γ.lam, y - x ∈ X := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam inferInstance hSD (orth (VS D) X) x
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl (fun p => (hLset p).symm.subset) hx hxo hmΛ hmU)
    refine ⟨w, hw, ?_⟩
    have h2 := X.neg_mem (hXX hxw)
    rwa [neg_sub] at h2
  have hL' : ∀ y ∈ γ.lam, y ∈ orth (VS D) X → ∃ x ∈ Λ₂, x ∈ orth (VS D) X ∧ y - x ∈ X := fun y hy hyo => by
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ inferInstance hSD₂ (orth (VS D) X) y
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl₂ (fun p => (hLset p).subset) hy hyo hmΛ hmU)
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) X).sub_mem hyo (hXo hX1)
  have hXm : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ γ.lam := fun x hx =>
    ⟨BwdNP.memX Zd γ hpr₂ hpr inferInstance hu hx, BwdNP.memX Zd γ hpr hpr₂ inferInstance hu hx⟩
  have hy := BwdNP.exists_y Zd γ (Λ₂ := Λ₂) inferInstance hSD₂ hpr₂ hu bwdN_znotX
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hiso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) X hXiso F0.z bwdN_zorth γ.lam Λ₂
    inferInstance inferInstance hSD hSD₂ hXm
    (BwdNP.z_mem Zd γ (Λ := γ.lam) inferInstance hpr) (BwdNP.z_mem Zd γ (Λ := Λ₂) inferInstance hpr₂) hL hL' hy htr
  refine ⟨n, ⟨hiso, fun j x hx => ?_, hno, fun a => hnX _ (Submodule.subset_span ⟨a, rfl⟩), hnz⟩, himg⟩
  have hxX : x ∈ X := Submodule.span_mono (Set.image_subset_range _ _) hx
  rw [hnX x hxX, sub_self]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaF

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdBeta'_of_leaves (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    BwdBeta' Zd u u' F0 what₂ :=
  bwdBeta'_of_core Zd repG_holds (betaCore_of₂ Zd (betaCore₂_of Zd hRat (scalarOf_holds Zd) hInt))

theorem fStarC_of_leaves' (hC : CtxP u u' F0 what₂) (hLP : LprPart Zd u u' F0 what₂)
    (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_route2 Zd (starExists2_holds Zd u u' F0 what₂ hC)
    (fwdC_of_loc Zd hC.2.1 (omega_part_holds Zd u u' F0 what₂) (genXi_holds Zd) hLP)
    (bwdC_of''' Zd hC (bwdN_holds Zd u u' F0 what₂) (bwdTerm'_holds Zd u u' F0 what₂) (bwdBeta'_of_leaves Zd hRat hInt))
    (Uniq.uniqC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end
