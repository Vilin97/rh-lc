module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutDeep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockCounting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SecondValueMul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ConjSecondFactor
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FCInj
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountAtOfParts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBaseT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumShift
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FCInj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolGrp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobPOfInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsCompactIntLowSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabApprox

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCellRel

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

def mkUP (X Y : MP p) (hX : IsLoUni X) (hY : IsUpUni Y) : UP p :=
  ⟨(uLo X (fun a b h => (hX a b).1 h) (fun a => (hX a a).2 rfl),
      MulOpposite.op (uUpU Y (fun a b h => (hY a b).1 h) (fun a => (hY a a).2 rfl))), hX, hY⟩

theorem fC_range : Set.range (fC M a πa hker g) =
    {c | ∃ pr : Formalism.L2.SG.Pf.Coef.CellPair a, Quotient.mk _ pr = c ∧
      pr.1.1 * a.mat * pr.1.2 ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) ((g : GG p) • a.mat)} := by
  ext c
  constructor
  · rintro ⟨X, rfl⟩
    induction X using Quotient.inductionOn with
    | h x =>
      obtain ⟨hxN, k, hk, hxk⟩ := x.2
      refine ⟨pairOfU a πa hker x.1 (MonoidHom.mem_ker.1 hxN), rfl, ?_⟩
      refine ⟨(((k : GG p).1 : GLp p)).val, (((k : GG p).2.unop : GLp p)).val, hk.1, hk.2, ?_⟩
      exact hxk
  · rintro ⟨pr, rfl, l, ρ, hl, hρ, he⟩
    have hv : IsLoUni pr.1.1 := fun i j => ⟨pr.2.1.2.1 i j, fun h => h ▸ pr.2.1.1 i⟩
    have hu : IsUpUni pr.1.2 := fun i j => ⟨pr.2.2.2 i j, fun h => h ▸ pr.2.2.1 i⟩
    set x := mkUP pr.1.1 pr.1.2 hv hu with hxdef
    have hxN : πa x = 1 := (hker x).2 ⟨hv, fun i j hij hb => pr.2.1.2.2 i j hij hb⟩
    set k := mkUP l ρ (Formalism.L2.SG.Pf.ProdEP2Cut.loUni_of_int M hl) (Formalism.L2.SG.Pf.ProdEP2Cut.upUni_of_int M hρ)
    have hk : k ∈ KU M p := ⟨hl, hρ⟩
    refine ⟨Quotient.mk _ ⟨x, MonoidHom.mem_ker.2 hxN, k, hk, he⟩, ?_⟩
    show Quotient.mk _ (pairOfU a πa hker x hxN) = _
    congr 1

include hker in
theorem card_cellRel : Nat.card (Quotient (CountAb.cellRel (a.mat) πa.ker (KU M p) g)) =
    {c : Quotient (Formalism.L2.SG.Pf.Coef.cellSetoid (M p) a) | ∃ pr : Formalism.L2.SG.Pf.Coef.CellPair a,
      Quotient.mk (Formalism.L2.SG.Pf.Coef.cellSetoid (M p) a) pr = c ∧
      pr.1.1 * a.mat * pr.1.2 ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) ((g : GG p) • a.mat)}.ncard := by
  rw [← fC_range M a πa hker g, Set.ncard_range_of_injective (fC_inj M a πa hker g)]

end Formalism.L2.SG.Pf.CountAt
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountWt

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf MeasureTheory
open Classical

variable {D : Formalism.BasicNotions.D7}

theorem wtL_eq_wtZ (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (ha : modPt δ T T' p w = some a) (Y : MatP D p) :
    wtL M δ T T' p w Y = wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) := by
  have hmat : a.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w a ha
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 ∈ kkOrb M p Y} =
      {xy | zAt a xy ∈ orbR (M p) (Y + shM δ T T' p w)} := by
    ext xy
    simp only [Set.mem_ofPred_eq]
    rw [mem_orbR_iff M δ T T' p w Y (zAt a xy), zAt_eq hmat xy, add_sub_cancel_right]
  unfold wtL wtZ muA
  simp only [ha]
  rw [hset]

theorem wtL_count (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (hOK : (M p).OK) (ha : modPt δ T T' p w = some a) {Y : MatP D p} (hY : ∀ i j, Y i j ∈ (M p).R) :
    {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.Finite ∧
    wtL M δ T T' p w Y = ({q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.ncard : ℝ) := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hZ0 : ∀ i j, (Y + shM δ T T' p w) i j ∈ (M p).R := fun i j =>
    add_mem (hY i j) (shM_mem M δ T T' p w i j)
  obtain ⟨hfin, hsum⟩ := LocOrbCut.wt_gen (M p) hOK a (Y + shM δ T T' p w) hZ0
  set S := {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)} with hSdef
  have hsupp : (Function.support (fun q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) =>
      if LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w) then (1 : ℂ) else 0)) = S := by
    ext q
    simp [hSdef]
  rw [hsupp] at hfin
  refine ⟨hfin, ?_⟩
  rw [wtL_eq_wtZ M δ ha Y]
  have hc : (wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) : ℂ) = (S.ncard : ℂ) := by
    rw [hsum, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [hsupp]; simp)]
    rw [Finset.sum_boole, Set.ncard_eq_toFinset_card S hfin]
    congr 2
    exact Finset.filter_true_of_mem (fun q hq => hfin.mem_toFinset.1 hq)
  exact_mod_cast hc

end Formalism.L2.SG.Pf.Coef
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XPEqZzp

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem XP_eq_ZZP {p : PlF D} (hA : Agree δ M p) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (heq : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U) :
    XP M δ u u' (p := p) w L U = Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') := by
  unfold XP Y0
  rw [← move δ M u u' hA L U hL hU, Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM, ← heq,
    Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM]

theorem int_zzp (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    ∀ i j, (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) i j ∈
      (M p).R := by
  obtain ⟨hAg, hT, hrows, -, hel, ⟨hPD, hmk⟩, hadm, -⟩ := hE
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := Formalism.L2.SG.TermDef.Gt_mk hTF.1 ⟨F', hPD⟩
  have hGen := Formalism.L2.SG.TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨F', hPD⟩
  rw [hmk] at hGt hGen
  have hEZ : F' ∈ Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') F0 γ.lam (ZhatL (lf D F0) F') :=
    ⟨⟨hPD.1, hPD.2.1, fun h => hel.1.2 (hGt.trans h)⟩, hadm, hGen.1 hel.1.1, hPD.2.2, rfl⟩
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hAg u u' hT F0 what₂ hrows γ.lam γ.mem (ZhatL (lf D F0) F') F' hEZ p
  intro i j
  simp only [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI i j) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.CountAt
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountAtHolds

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbR_stable {p : PlF D} (Z0 : MP p) :
    ∀ Z ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0, ∀ l ρ, Formalism.MainNotions.S.TieN.IntLow (M p) l → Formalism.MainNotions.S.TieN.IntUp (M p) ρ →
      l * Z * ρ ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0 := by
  rintro Z ⟨l', ρ', hl', hρ', rfl⟩ l ρ hl hρ
  refine ⟨l * l', ρ' * ρ, Formalism.L2.SG.Pf.LocOrbCut.intLow_mul (M p) hl hl', Formalism.L2.SG.Pf.LocOrbCut.intUp_mul (M p) hρ' hρ, ?_⟩
  simp only [Matrix.mul_assoc]

theorem countAt_holds (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) := by
  have hA := hE.1 p
  have hL := hE.2.2.2.2.2.2.2.1
  have hU := hE.2.2.2.2.2.2.2.2.1
  have heq := hE.2.2.2.2.2.2.2.2.2
  obtain ⟨a, ha⟩ := Formalism.L2.SG.Pf.PCount.modPt_full (δ := δ) (D.mem u).A.T (D.mem u').A.T p hA.2.1 w
  obtain ⟨πa, hD, hker⟩ := blockRetr_holds M a
  have hB := baseAt_holds M δ u u' w p hE.1 a ha
  have hInt := int_zzp M δ u u' F0 what₂ γ w F' L U hE p
  have hgW : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
      Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
        Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [gU_smul, XP_eq_ZZP M δ u u' F0 hA w F' L U hL hU heq]
    rfl
  obtain ⟨hfin, hwt⟩ := Formalism.L2.SG.Pf.Coef.wtL_count M δ hA.1 ha hInt
  have hcard := card_cellRel M a πa hker (gU M δ u u' w hA L U hL hU a hB)
  rw [hgW] at hcard
  set Z0 : MP p := Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
    Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w with hZ0
  have hcos := Formalism.L2.SG.Pf.Coef.cellCos (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0) (orbR_stable M Z0)
  refine countAt_of_parts M δ u u' w hA L U hL hU a hB πa hD _ ?_ ?_
  · rw [hcard, ← hcos, hwt]
  · rw [Nat.card_ne_zero]
    refine ⟨⟨Quotient.mk _ (CountAb.toCell a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
      (gU M δ u u' w hA L U hL hU a hB) hD 1)⟩, ?_⟩
    have hcl := (Formalism.L2.SG.Pf.Coef.cellCos_finite_iff (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0)
      (orbR_stable M Z0)).1 hfin
    have hrange := fC_range M a πa hker (gU M δ u u' w hA L U hL hU a hB)
    rw [hgW] at hrange
    rw [← hrange] at hcl
    have hinj : Function.Injective (Set.rangeFactorization (fC M a πa hker (gU M δ u u' w hA L U hL hU a hB))) :=
      fun x y h => fC_inj M a πa hker _ (congrArg Subtype.val h)
    exact @Finite.of_injective _ _ hcl.to_subtype _ hinj

end Formalism.L2.SG.Pf.CountAt
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCut

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutLeavesDeep_of_betaInt (D : Formalism.BasicNotions.D7)
    (hB : ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
      (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
      (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)), BetaInt ⟨δ, M, hA⟩ u u' F0 what₂) :
    Formalism.L2.SG.Pf.Coef.CutLeavesDeep D := by
  intro _ δ M hA _ u u' hc hP F0 what₂ hR
  refine ⟨fun γ w F' L U hE p => ⟨Formalism.L2.SG.Pf.CountAt.countAt_holds (M := M) (δ := δ) (γ := γ) (w := w) (F' := F') (L := L) (U := U) (hE := hE) (p := p) ..,
    by intros; apply Formalism.L2.SG.Pf.ProdEP2Uni.unimodAt_holds⟩,
    Formalism.L2.SG.Pf.TupGlobApprox.stabApprox _ u u', ?_⟩
  exact fStarC_of_int ⟨δ, M, hA⟩ ⟨hc, hR, hP⟩ (hB δ M hA u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
end
