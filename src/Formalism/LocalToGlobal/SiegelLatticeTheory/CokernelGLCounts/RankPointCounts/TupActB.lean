module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolAct
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameShapeHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneMemDdPow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfSk
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupGlob
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DdPowConj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdSPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NotDvdDiff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.DiffIdealNeBot
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupLift
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupLift
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCong
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFS
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupAct

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupAct

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Pf.TupOrb
  Formalism.L2.SG.Pf.TupLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lift_move {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) (hu : Tu D u ≠ 0) (hu' : Tu D u' ≠ 0)
    {t : TermsOf D u' F0 Λ} {Z₁ : PairVal.MatR D} {F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (h₁ : F₁ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁)
    (r₁ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁)
    {U U' : PairVal.MatR D} (hU : IsUpUni U) (hU' : IsUpUni U') (hiU : TupGlob.IntFr U) (hiU' : TupGlob.IntFr U')
    (htie : TupGlob.TieG U U') :
    ∃ ν ∈ NLam Λ (lf D F0), ∃ m ∈ NLam Λ F₁,
      (∀ b, ν (frame (lf D F0) b) = ∑ c, U c b • frame (lf D F0) c) ∧
      (∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c) ∧
      ∃ F2 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ (U.conjTranspose * Z₁ * U'),
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F2 ∧ ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := by
  obtain ⟨p₁, e₁⟩ := r₁
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 Λ hΛ
  obtain ⟨ν, hν, hνF⟩ := TupOnto.nLamOnto_holds D u F0 Λ hΛ hu U hU hiU
  obtain ⟨m, hm, hmF⟩ := TupOnto.nLamOnto_holds D u' F₁.fl Λ (isRowLat_of_pd hΛ p₁) hu' U' hU' hiU'
  have hm' : m ∈ NLam Λ F₁ := hm
  have hmF' : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c := hmF
  have hAut : IsAutLam (VS D) Λ (ν⁻¹ * m) :=
    Formalism.L2.SG.Pf.isAutLam_mul (Formalism.L2.SG.Pf.isAutLam_inv hν.1) hm.1
  let F2 := Formalism.L2.SG.Saturated.mapL (ν⁻¹ * m) hAut.1 F₁
  have hf2 : ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := fun b => by
    rw [Formalism.L2.SG.Saturated.frame_mapL]; rfl
  have hdc : DCRel Λ (lf D F0) F₁ F2 := ⟨ν⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hν, m, hm', hf2, rfl⟩
  have pd2 : PD D Λ (lf D F0) u' F2 := Formalism.L2.SG.Closed.TermStable_holds D u u' F0 Λ hΛ ⟨F₁, p₁⟩ F2 hdc
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hu'
  have hFΛ : ∀ c, frame (lf D F0) c ∈ Λ := by
    intro c
    refine Fin.lastCases ?_ (fun a => ?_) c
    · rw [Formalism.L2.SG.Pf.frame_last_td]; exact hΛ.2.1.2.2.1.1
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td]; exact PI.NRL.e_mem_lam D F0 Λ hΛ a
  have hiso : ∀ x y, (VS D).hT (ν x) (ν y) = (VS D).hT x y := ((Formalism.L2.SG.Pf.isAutLam_iff Λ ν).1 hν.1).1
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F2 b) =
      (U.conjTranspose * ZhatL (lf D F0) F₁ * U') a b := fun a b => by
    rw [hf2 b]; exact zhat_lift (lf D F0) F₁ hiso hνF hmF' a b
  refine ⟨ν, hν, m, hm', hνF, hmF', F2, ⟨⟨pd2.1, pd2.2.1, ?_⟩, ?_, ?_, pd2.2.2, ?_⟩,
    ⟨pd2, (Quot.sound (show TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F₁, p₁⟩ ⟨F2, pd2⟩ from hdc)).symm.trans e₁⟩, hf2⟩
  · change Gval (lf D F0) F2 ≠ 0
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact h₁.1.2.2
  · refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    rw [frameAct_one']
    change ModG (VS D) Λ (Lat.gS D) (frame F2 b - frame (lf D F0) b)
    rw [hf2 b]
    exact modG_lift hT' p₁.1 p₁.2.2.1 hFΛ hν.1 hm' hνF hmF' htie
      (fun c => by have := h₁.2.1.2.2 c; rwa [frameAct_one'] at this) b
  · exact (hFun.2.2.2.1 ⟨F₁, p₁⟩ ⟨F2, pd2⟩ hdc).1 h₁.2.2.1
  · have hZZ : ZhatL (lf D F0) F2 = U.conjTranspose * ZhatL (lf D F0) F₁ * U' := by
      funext a b
      exact hent a b
    change ZhatL (lf D F0) F2 = U.conjTranspose * Z₁ * U'
    have hz1 : ZhatL (lf D F0) F₁ = Z₁ := h₁.2.2.2.2
    rw [hZZ, hz1]

theorem integral_pair_of_shape (Zd : Formalism.L2.SG.TermLoc.LocDat D) {A B : PairVal.MatR D} (hA : Formalism.L2.SG.Pf.AtPt.IsLo A)
    (hB : Formalism.L2.SG.Pf.AtPt.IsUp B) (hES : Formalism.L2.SG.Pf.StabIntSh.EntryShape D A B) :
    TupGlob.IntFr A.conjTranspose ∧
      TupGlob.IntFr (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) ∧
      TupGlob.TieG A.conjTranspose
        (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) := by
  open Formalism.L2.SG.Pf.FibD in
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

theorem ez_of_normRep {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {γ : TermDef.Term D u u' F0 what₂}
    (hΛ : IsRowLat D F0 γ.lam) {w w₁ : Point D.host.E (D.R.rS + 1)} (hel : Formalism.L2.SG.DataCut.EligAt γ w)
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)} {L U : PairVal.MatR D}
    (hn : PairVal.NormRep γ w₁ F' L U) :
    F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F') := by
  obtain ⟨⟨p₁, e₁⟩, hadm₁, -⟩ := hn
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam hΛ
  obtain ⟨Fa, ⟨pa, ea⟩, hGa, -⟩ := hel.2
  have hdca := (hEq ⟨Fa, pa⟩ ⟨F', p₁⟩).1 (ea.trans e₁.symm)
  obtain ⟨Fg, ⟨pg, eg⟩, hgen⟩ := hel.1.1
  refine ⟨⟨p₁.1, p₁.2.1, ?_⟩, hadm₁, ?_, p₁.2.2, rfl⟩
  · change Gval (lf D F0) F' ≠ 0
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca]; exact hGa
  · exact (hFun.2.2.2.1 ⟨Fg, pg⟩ ⟨F', p₁⟩ ((hEq ⟨Fg, pg⟩ ⟨F', p₁⟩).1 (eg.trans e₁.symm))).1 hgen

theorem moveCZ {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) (hu : Tu D u ≠ 0) (hu' : Tu D u' ≠ 0)
    (Zd : Formalism.L2.SG.TermLoc.LocDat D) {t : TermsOf D u' F0 Λ} {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (h' : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z)
    (r' : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F')
    {a' b : PairVal.MatR D} (ha : IsLoUni a') (hb : IsUpUni b) (hst : a' * ZhatOM Z * b = ZhatOM Z)
    (hES : Formalism.L2.SG.Pf.StabIntSh.EntryShape D a' b) :
    ∃ ν ∈ NLam Λ (lf D F0), ∃ m ∈ NLam Λ F',
      (∀ c, ν (frame (lf D F0) c) = ∑ d, a'.conjTranspose d c • frame (lf D F0) d) ∧
      (∀ c, m (frame F' c) = ∑ d, (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * b * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) d c •
        frame F' d) ∧
      ∃ F2 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F2 ∧ ∀ c, frame F2 c = ν⁻¹ (m (frame F' c)) := by
  set Sg := Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS with hSg
  have hlo : Formalism.L2.SG.Pf.AtPt.IsLo a' := ⟨fun i => (ha i i).2 rfl, fun i j h => (ha i j).1 h⟩
  have hup : Formalism.L2.SG.Pf.AtPt.IsUp b := ⟨fun i => (hb i i).2 rfl, fun i j h => (hb j i).1 h⟩
  obtain ⟨hi1, hi2, htie⟩ := integral_pair_of_shape Zd hlo hup hES
  have hU : IsUpUni a'.conjTranspose := fun i j => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [Matrix.conjTranspose_apply, (ha j i).1 h, star_zero]
    · subst h; rw [Matrix.conjTranspose_apply, (ha i i).2 rfl, star_one]
  have hU' : IsUpUni (Sg * b * Sg) := fun i j => by
    rw [Formalism.L2.SG.Pf.FibD.sg_entry]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp [Formalism.L2.SG.Pf.StabIntSh.bt, (hb i j).1 h]
    · subst h
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, (hb i i).2 rfl, ← pow_add, ← two_mul, pow_mul]
  obtain ⟨ν, hν, m, hm, hνF, hmF, F2, hF2, hr2, hf2⟩ := lift_move hΛ hu hu' h' r' hU hU' hi1 hi2 htie
  refine ⟨ν, hν, m, hm, hνF, hmF, F2, ?_, hr2, hf2⟩
  have hZ : a'.conjTranspose.conjTranspose * Z * (Sg * b * Sg) = Z := by
    rw [Matrix.conjTranspose_conjTranspose]
    have hS : ZhatOM Z = Z * Sg := Formalism.L2.SG.Pf.AtPt.zhatOM_eq Z
    rw [hS] at hst
    calc a' * Z * (Sg * b * Sg) = (a' * (Z * Sg) * b) * Sg := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [hst, Matrix.mul_assoc, Formalism.L2.SG.Pf.AtPt.sg_sq, Matrix.mul_one]
  rwa [hZ] at hF2

end Formalism.L2.SG.Pf.TupAct
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupActB

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.TupActB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem cong_at_pair {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hz' : F'.fl.z ∈ Λ) (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hν : ∀ v ∈ Λ, ν v ∈ Λ) (hm : ∀ v ∈ Λ, m v ∈ Λ)
    (F'' : LFlag (D.sp.Y 0) D.R.rS T') (hadm'' : ∀ b, ModG (VS D) Λ (Lat.gS D) (F''.fl.fvec b - F.fl.fvec b))
    (hf'' : ∀ b, F''.fl.fvec b = ν⁻¹ (m (F'.fl.fvec b)))
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, ν (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, m (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E,
      (t : D.host.E) * (uu j i - uu' j i) = ((Lat.gS D : ℕ) : D.host.E) * o := by
  have hP := P.isPrime
  set g : 𝓞 D.host.E := ((Lat.gS D : ℕ) : 𝓞 D.host.E) with hg
  set M := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {g} • Λ) with hM
  have hg0 : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by
    have h2 : (Lat.gS D : ℕ) ≠ 0 := by
      unfold Lat.gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast h2

  have hgs : ∀ x : (VS D).V, x ∈ Ideal.span {g} • Λ ↔ ∃ l ∈ Λ, g • l = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  have hd : ∀ c, F'.fl.fvec c - F.fl.fvec c ∈ M := fun c => hadm c P hgP
  have hsd : m (F'.fl.fvec i) - ν (F.fl.fvec i) ∈ M := by
    have e : m (F'.fl.fvec i) - ν (F.fl.fvec i) = ν (F''.fl.fvec i - F.fl.fvec i) := by
      rw [map_sub, hf'' i]
      simp [LinearEquiv.coe_inv]
    rw [e]
    obtain ⟨t, ht, htd⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 (hadm'' i P hgP)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).2 ⟨t, ht, ?_⟩
    rw [← Formalism.L2.SG.Pf.ZsVolLat.smul_O, ← hlg, Formalism.L2.SG.Pf.ZsVolLat.smul_O]
    exact (hgs _).2 ⟨ν l, hν l hl, rfl⟩
  have hud : ∀ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) ∈ M := by
    intro c
    obtain ⟨t1, ht1, o, ho⟩ := Formalism.L2.SG.Pf.ZsVolLat.int_at F' Λ hc' hz' m hm uu' huu' hfr' P hgP c i
    obtain ⟨t2, ht2, htd⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 (hd c)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).2 ⟨t1 * t2, fun h => (hP.mem_or_mem h).elim ht1 ht2, ?_⟩
    have e : (t1 * t2) • (uu' c i • (F'.fl.fvec c - F.fl.fvec c)) = o • (t2 • (F'.fl.fvec c - F.fl.fvec c)) := by
      rw [← algebraMap_smul D.host.E (t1 * t2), ← algebraMap_smul D.host.E o, ← algebraMap_smul D.host.E t2, smul_smul,
        smul_smul]
      have ho' : algebraMap (𝓞 D.host.E) D.host.E t1 * uu' c i = algebraMap (𝓞 D.host.E) D.host.E o := ho
      rw [map_mul, mul_right_comm, ho']
    rw [e, ← hlg]
    exact (hgs _).2 ⟨o • l, Λ.smul_mem o hl, smul_comm g o l⟩

  set y : Fin D.R.rS → D.host.E := fun a => uu' (Fin.castSucc a) i - uu (Fin.castSucc a) i with hy
  have hlast : uu' (Fin.last _) i - uu (Fin.last _) i = 0 := by
    by_cases h : i = Fin.last _
    · subst h
      rw [(huu' _ _).2 rfl, (huu _ _).2 rfl, sub_self]
    · have hlt : i < Fin.last _ := lt_of_le_of_ne (Fin.le_last i) h
      rw [(huu' _ _).1 hlt, (huu _ _).1 hlt, sub_self]
  have hw : ∑ a, y a • F.fl.e a = (m (F'.fl.fvec i) - ν (F.fl.fvec i)) - ∑ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) := by
    rw [hfr i, hfr' i]
    simp only [smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ c, (uu' c i - uu c i) • F.fl.fvec c = ∑ a, y a • F.fl.e a := by
      rw [Formalism.L2.SG.Pf.ZsVolLat.sum_fvec]
      simp only [hy, hlast, zero_smul, add_zero]
    rw [← h2]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  have hwM : ∑ a, y a • F.fl.e a ∈ M := by
    rw [hw]
    exact M.sub_mem hsd (M.sum_mem fun c _ => hud c)
  obtain ⟨t, ht, htw⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 hwM
  obtain ⟨l, hl, hlg⟩ := (hgs _).1 htw

  have hl_eq : l = ∑ a, (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a)) • F.fl.e a := by
    have h1 : ((Lat.gS D : ℕ) : D.host.E) • l = t • ∑ a, y a • F.fl.e a := by
      rw [← hlg, ← algebraMap_smul D.host.E g]
      rfl
    have h2 := congrArg (fun v => ((Lat.gS D : ℕ) : D.host.E)⁻¹ • v) h1
    simp only [smul_smul, inv_mul_cancel₀ hg0, one_smul] at h2
    rw [h2, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t, smul_smul, smul_smul, mul_assoc]
  have hlX : l ∈ XLam Λ F := by
    refine Submodule.mem_inf.2 ⟨hl, ?_⟩
    show l ∈ F.fl.X
    rw [hl_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hloc : l ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
    rw [← Formalism.L2.SG.Pf.ZsVolLat.conv_at F Λ hc P hgP]
    exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hlX⟩
  obtain ⟨t', ht', ht'l⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 hloc
  have hv2 : t' • l = ∑ a, ((t' : D.host.E) * (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a))) • F.fl.e a := by
    rw [hl_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t', smul_smul]
  have hjr : (j : ℕ) < D.R.rS := lt_of_lt_of_le hji (Nat.lt_succ_iff.1 i.2)
  obtain ⟨o, ho⟩ := Formalism.L2.SG.Pf.ZsVolLat.coef_spanO F.fl ht'l _ hv2 ⟨j, hjr⟩
  refine ⟨t' * t, fun h => (hP.mem_or_mem h).elim ht' ht, -o, ?_⟩
  have hyj : y ⟨j, hjr⟩ = uu' j i - uu j i := rfl
  rw [hyj] at ho
  have hgi : ((Lat.gS D : ℕ) : D.host.E) * ((Lat.gS D : ℕ) : D.host.E)⁻¹ = 1 := mul_inv_cancel₀ hg0
  push_cast
  linear_combination ((Lat.gS D : ℕ) : D.host.E) * ho + ((t' : D.host.E) * (t : D.host.E) * (uu' j i - uu j i)) * hgi

theorem cong_glob_pair {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hX : XLam Λ F = XS D F.fl) (hX' : XLam Λ F' = XS D F'.fl) (hz : F.fl.z ∈ Λ) (hz' : F'.fl.z ∈ Λ)
    (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hν : ∀ v ∈ Λ, ν v ∈ Λ) (hm : ∀ v ∈ Λ, m v ∈ Λ)
    (F'' : LFlag (D.sp.Y 0) D.R.rS T') (hadm'' : ∀ b, ModG (VS D) Λ (Lat.gS D) (F''.fl.fvec b - F.fl.fvec b))
    (hf'' : ∀ b, F''.fl.fvec b = ν⁻¹ (m (F'.fl.fvec b)))
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, ν (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, m (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D ((i : ℕ) - (j : ℕ)) := by
  have h1 : uu j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) := Formalism.L2.SG.Pf.ZsVolLat.frame_entry F Λ hX hz ν hν uu huu hfr j i hji
  have h2 : uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    Formalism.L2.SG.Pf.ZsVolLat.frame_entry F' Λ hX' hz' m hm uu' huu' hfr' j i hji
  have hd : uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    (FractionalIdeal.mem_coe).1 (Submodule.sub_mem _ ((FractionalIdeal.mem_coe).2 h1) ((FractionalIdeal.mem_coe).2 h2))
  refine (FractionalIdeal.mem_coe).1 (Formalism.L2.SG.Pf.ZsVolLat.mem_of_loc _ _ fun P => ?_)
  by_cases hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨t, ht, o, ho⟩ := cong_at_pair F F' Λ hc hc' hz' hadm ν m hν hm F'' hadm'' hf'' uu uu' huu huu' hfr hfr' P hgP j i hji
    refine ⟨t, ht, ?_⟩
    rw [ho]
    exact (FractionalIdeal.mem_coe).2 (Formalism.L2.SG.Pf.ZsVolLat.g_mul_mem (Formalism.L2.SG.Pf.ZsVolLat.o_mem_ddPow _ o))
  · refine ⟨((Lat.gS D : ℕ) : 𝓞 D.host.E), hgP, ?_⟩
    have e : (((Lat.gS D : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Lat.gS D : ℕ) : D.host.E) := by simp
    rw [e]
    exact (FractionalIdeal.mem_coe).2 (Formalism.L2.SG.Pf.ZsVolLat.g_mul_mem hd)

variable (M : ∀ p : LocalSplitGroups.PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : LocalSplitGroups.PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem moveCZ_holds : Formalism.L2.SG.Pf.ZsVolAct.MoveCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH a' b ha hb hst hES
  obtain ⟨hA, -, hR, hP, hE, hN⟩ := hH
  have hΛ : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  have h' := Formalism.L2.SG.Pf.TupAct.ez_of_normRep hΛ hE hN
  obtain ⟨p', e'⟩ := hN.1
  obtain ⟨ν, hν, m, hm, hνF, hmF, F2, hF2, hr2, hf2⟩ :=
    Formalism.L2.SG.Pf.TupAct.moveCZ hΛ hP.1.ne_zero hP.2.2.1.ne_zero ⟨δ, M, hA⟩ h' ⟨p', e'⟩ ha hb hst hES
  exact ⟨ν, m, F2, ha, hb, hst, hES, hν, hm, hνF, hmF, hF2, hr2, hf2⟩

theorem ontoCZ_holds : Formalism.L2.SG.Pf.ZsVolAct.OntoCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH F'' hF'' hr''
  obtain ⟨hA, -, hR, hP, hE, hN⟩ := hH
  have hΛ : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  obtain ⟨_, ⟨_, _, hLift, hConv⟩, hXF⟩ := hΛ
  obtain ⟨⟨⟨hLift', _, hFOK⟩, e'⟩, hAdm, _, _, _⟩ := hN
  obtain ⟨p'', e''⟩ := hr''
  obtain ⟨n, hn, m, hm, hfr, -⟩ := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam (hR.1 γ.lam γ.mem)
    ⟨F', ⟨hLift', ‹_›, hFOK⟩⟩ ⟨F'', p''⟩).1 (e'.trans e''.symm)
  have hν : n⁻¹ ∈ NLam γ.lam (lf D F0) := Formalism.L2.SG.Pf.nlamPf_inv hn
  have hf'' : ∀ b, F''.fl.fvec b = (n⁻¹)⁻¹ (m (F'.fl.fvec b)) := fun b => by rw [inv_inv]; exact hfr b
  have hν0 := hν
  have hm0 := hm
  obtain ⟨⟨hisoν, hgν⟩, hf1, hf2⟩ := hν
  obtain ⟨uu, huu, hu⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 n⁻¹ hf1 hf2
  obtain ⟨⟨hisom, hgm⟩, hg1, hg2⟩ := hm
  obtain ⟨uu', huu', hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl m hg1 hg2
  have hνΛ : ∀ v ∈ γ.lam, n⁻¹ v ∈ γ.lam := fun v hv => by
    rw [← hgν]; exact Submodule.mem_map_of_mem hv
  have hmΛ : ∀ v ∈ γ.lam, m v ∈ γ.lam := fun v hv => by
    rw [← hgm]; exact Submodule.mem_map_of_mem hv
  have hdet : IsUnit uu.conjTranspose.det := by
    rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu)]; exact isUnit_one
  let a' : PairVal.GLR D := Matrix.nonsingInvUnit uu.conjTranspose hdet
  have ha' : (a' : PairVal.MatR D) = uu.conjTranspose := rfl
  have hSS : Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM (K := D.host.E) D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS = 1 :=
    Formalism.L2.SG.Pf.AtPt.sg_sq D.R.rS
  let b : PairVal.MatR D := Formalism.L2.SG.Pf.ZsVolAct.sbs uu'
  have hsbs : Formalism.L2.SG.Pf.ZsVolAct.sbs b = uu' := by
    simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs, Matrix.mul_assoc]
    rw [hSS, Matrix.mul_one, ← Matrix.mul_assoc, hSS, Matrix.one_mul]
  have hbU : IsUpUni b := by
    intro i j
    simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs, Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]
    refine ⟨fun h => by rw [(huu' i j).1 h, mul_zero, zero_mul], fun h => ?_⟩
    subst h
    rw [(huu' i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp
  have hiso : ∀ x y, (VS D).hT ((n⁻¹) x) ((n⁻¹) y) = (VS D).hT x y := hisoν
  have hZ1 : uu.conjTranspose * ZhatL (lf D F0) F' * uu' = ZhatL (lf D F0) F' := by
    have hZ'' : ZhatL (lf D F0) F'' = ZhatL (lf D F0) F' := hF''.2.2.2.2
    funext a c
    rw [← Formalism.L2.SG.Pf.TupLift.zhat_lift (lf D F0) F' hiso hu hu' a c, ← hZ'']
    show (VS D).hT (F0.fvec a) ((n⁻¹)⁻¹ (m (F'.fl.fvec c))) = (VS D).hT (F0.fvec a) (F''.fl.fvec c)
    rw [hf'' c]
  have hadm : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F'.fl.fvec b - (lf D F0).fl.fvec b) := fun b => by
    have h := hAdm.2.2 b
    rwa [Formalism.L2.SG.Pf.TupOrb.frameAct_one'] at h
  have hadm'' : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F''.fl.fvec b - (lf D F0).fl.fvec b) := fun b => by
    have h := hF''.2.1.2.2 b
    rwa [Formalism.L2.SG.Pf.TupOrb.frameAct_one'] at h
  refine ⟨a', b, n⁻¹, m, ?_, hbU, ?_, ?_, hν0, hm0, ?_, ?_, hF'', ⟨p'', e''⟩, hf''⟩
  · rw [ha']; exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu
  · rw [ha', Formalism.L2.SG.Pf.AtPt.zhatOM_eq]
    calc uu.conjTranspose * (ZhatL (lf D F0) F' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) * b
        = uu.conjTranspose * ZhatL (lf D F0) F' * (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * b) := by
          simp only [Matrix.mul_assoc]
      _ = uu.conjTranspose * ZhatL (lf D F0) F' * uu' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS := by
          have : Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * b = uu' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS := by
            simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs, ← Matrix.mul_assoc]
            show Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS = _
            rw [hSS, Matrix.one_mul]
            rfl
          rw [this]; simp only [Matrix.mul_assoc]
      _ = ZhatL (lf D F0) F' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS := by rw [hZ1]
  · intro i j hji
    have hk : ((i : ℕ) - (j : ℕ)) ≤ D.R.rS := by have := i.2; omega
    have h1 := Formalism.L2.SG.Pf.ZsVolLat.frame_entry (lf D F0) γ.lam hXF hLift.1 n⁻¹ hνΛ uu huu hu j i hji
    have h2 := Formalism.L2.SG.Pf.ZsVolLat.frame_entry F' γ.lam hFOK.2 hLift'.1 m hmΛ uu' huu' hu' j i hji
    have h3 := cong_glob_pair (lf D F0) F' γ.lam hConv hFOK.1 hXF hFOK.2 hLift.1 hLift'.1 hadm n⁻¹ m hνΛ hmΛ F''
      hadm'' hf'' uu uu' huu huu' hu hu' j i hji
    rw [ha']
    simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs]
    rw [Matrix.conjTranspose_apply, Formalism.L2.SG.Pf.ZsVolLat.bt_sgn, Formalism.L2.SG.Pf.ZsVolLat.star_conjF]
    refine ⟨Formalism.L2.SG.Pf.ZsVolLat.conj_ddPow δ M hA hk h1, h2, ?_⟩
    rw [← map_sub]
    exact Formalism.L2.SG.Pf.ZsVolLat.conj_qdPow δ M hA hk h3
  · intro c
    rw [ha', Matrix.conjTranspose_conjTranspose]
    exact hu c
  · intro c
    rw [hsbs]
    exact hu' c

end Formalism.L2.SG.Pf.TupActB

end
end
end
