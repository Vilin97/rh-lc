module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValid
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadCharacterBound

section

@[expose] public section

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField


open Classical in
def BadOfBase (B : Arith.Base) (h : ℕ → B.H) (Cb : ℝ) : Prop :=
  let PR := (Finset.range ⌈B.sc.X'⌉₊).filter (fun p =>
    p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ))
  ∑ p ∈ PR, Real.log p / p *
      ((B.TT.filter (fun t => ¬ Arith.Loc.Good B (h p) (Arith.bsH (Arith.Loc.stepP B (h p) p) t))).card : ℝ) ≤
    4 * (Cb * B.sc.x ^ (-2 : ℝ)) * B.sc.delta1 * B.R.n * ∑ p ∈ PR, Real.log p / p

theorem badOK_iff_badOfBase {R : Ranks} (s : Scale) (Cb : ℝ) (H : Host R) :
    BadOK s Cb H ↔ BadOfBase (baseOf s 0 0 H) (hPH H) Cb := Iff.rfl

theorem chBad_iff_badOfBase {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (hX : ∀ h t, X.bs h t = Arith.bsH h t) (Cb : ℝ) :
    ChBad_at X Cb ↔ BadOfBase (baseOf L.sc 0 0 D.host) (G.hP D) Cb := by
  have hb : X.bs = fun h t => Arith.bsH h t := funext fun h => funext fun t => hX h t
  unfold ChBad_at badTops
  obtain ⟨bs, h1, h2, off, h3, h4, h5, kap, ep⟩ := X
  dsimp only at hb
  subst hb
  exact Iff.rfl

theorem badOfBase_of_host {R R' : Ranks} (hR : R' = R) (s : Scale) (H : Host R) (H' : Host R')
    (h : ℕ → R.A) (h' : ℕ → R'.A) (Cb : ℝ)
    (hT : H'.TT.image Formalism.HC.Frame.A.val = H.TT.image Formalism.HC.Frame.A.val) (hq : H'.q = H.q) (hd : H'.d = H.d)
    (hc : H'.cls = H.cls)
    (hh : ∀ l, (h' l).val = (h l).val) (hb : BadOfBase (baseOf s 0 0 H) h Cb) :
    BadOfBase (baseOf s 0 0 H') h' Cb := by
  subst hR
  have hT' : H'.TT = H.TT := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hT
  have hh' : h' = h := funext fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  subst hh'
  unfold baseOf at hb ⊢
  rw [hT', hq, hd, hc]
  exact hb

theorem chBad_of_from : ∀ (C : FC) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ)
    (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ) (Cb : ℝ),
    p.From H a b c u0 → CanonInst p.ta.Gx → BadOK p.L.sc Cb H → ChBad_at p.ta.Gx Cb := by
  intro C p R H a b M c u0 Cb hF hC hB
  have hc := hF.cls_eq
  obtain ⟨hR, hT, -, hq, hd, -, -, -, -, -, hh, -⟩ := hF
  exact (chBad_iff_badOfBase _ hC.1 Cb).2
    (badOfBase_of_host hR p.L.sc H p.D.host (hPH H) (G.hP p.D) Cb hT hq hd hc hh ((badOK_iff_badOfBase _ _ _).1 hB))

end GlobalTheory.EX

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasWithDutyWallAndChoices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem has_withDuty_wall_and_choices {Q : PtProp} {C : FC} {cD ch C8 C5 c6 Cb : ℝ} (p : Pt C) {R : Ranks} {H : Host R} {q0 : ℕ}
    {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (hC : Std C) (hT : H.CT2 = C.CT2)
    (hH : HostGood p.L.sc C8 C5 c6 Cb H q0) (hq : (q0 : ℝ) < p.L.sc.X')
    (h0 : ∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) (hW : WOK p.L.sc cD ch C.GK H a b)
    (hV : Val C cD ch p.L) (hF : p.From H a b c u0) (hI : CanonInst p.ta.Gx) (hQ : p.Has Q) :
    p.Has ((withDuty Q).and WallPt) ∧ ThickSetLowerBound p.L ∧ ChBad_at p.ta.Gx Cb ∧ ChQD_at p.D p.L.sc.x p.L.sc.eps C5 := by
  have hw := GlobalTheory.EX.wreq_of_wok C cD ch p R H a b M c u0 hC hV hF hI h0 hW
  obtain ⟨hv, -, hT2, -, hQD, hBox, -, -, hBad, -, -, -, ⟨hp, hmod, -, hne, hne'⟩, hlev⟩ := hH
  have hb := GlobalTheory.EX.chBad_of_from C p R H a b M c u0 Cb hF hI hBad
  have eS := hF.QS_eq
  have hBW := hF.boxesW hBox
  have hQW := hF.qdRowsW hBox
  obtain ⟨eR, -, eT2, eq, ed, eg, ep, ep', hsub, -⟩ := hF
  subst eR
  have hq0 : (0 : ℝ) < q0 := by exact_mod_cast hp.pos
  have hXb := X'_le_b p.L.sc
  refine ⟨⟨⟨hQ, hw, ?_, ?_, q0, hsub (by rw [hlev]; simp), hp, ?_, ?_, hq, ?_, ?_, ?_⟩,
    ⟨hV.mem_box.1, hV.mem_box.2, hw⟩⟩, ?_, hb, ?_⟩
  · exact hBW
  · exact hQW
  · rw [eS, eq, ed]; exact hmod
  · rw [Real.log_le_iff_le_exp hq0]
    exact hq.le.trans hXb
  · rw [ep]; exact hne
  · rw [ep']; exact hne'
  · intro i hi
    have hg := (hv.2.2.2.2.1 i).1
    rw [← eg, ← hi] at hg
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  · unfold ThickSetLowerBound Host.secondSet_card_lower_bound
    rw [eT2, hV.secondConstant_eq, hV.host.2.2.2.2.2.1, ← hT, ← hv.2.2.2.2.2.1]
    exact hT2
  · unfold ChQD_at
    rw [eq, ed]
    exact hQD

end GlobalTheory.EX.DC
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.KitS

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

open GlobalTheory.Fc

theorem kitS : ∀ (Q : Par → PtProp) (la : ℝ) (G : FReq), DC.HostWW la G.req → ObjCP Q →
    KitCPW la (fun κ => ((withDuty (Q κ)).and DC.WallPt).and G.pt) := by
  intro Q la G hHost hObj
  obtain ⟨εH, hεH, hHost⟩ := hHost
  obtain ⟨εO, hεO, hObj⟩ := hObj
  refine ⟨min εH εO, lt_min hεH hεO, fun eps he he0 he1 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, KW, h8, h5, h6, hb, hHost⟩ := hHost eps he (he0.trans (min_le_left _ _)) he1
  obtain ⟨KO, hObj⟩ := hObj eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he1 h8
  refine ⟨CT2, C8, C5, c6, Cb, KW.sup KO, h8, h5, h6, hb, fun C hC hT hP hL => ?_⟩
  obtain ⟨hLW, hLO⟩ := fc_large_of_sup hL
  obtain ⟨c1, hObj⟩ := hObj C hC hP hLO
  obtain ⟨c1', hHost⟩ := hHost C hC hT hP hLW
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hObj⟩ := hObj cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hHost⟩ := hHost cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hObj⟩ := hObj ch ((le_max_left _ _).trans hch)
  obtain ⟨xH, S, hHost⟩ := hHost ch ((le_max_right _ _).trans hch)
  have hmid := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG : 0 ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hF : 0 ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xC, hCode⟩ := exists_injective_words eps C.CGam C.P.CF he he1 hG hF
  obtain ⟨xq, hq⟩ := small_prime_lt eps C8 he h8
  refine ⟨max (max xH xO) (max xC xq), S, fun s hs hx hmem => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxH, hxO⟩, hxC, hxq⟩ := hx
  obtain ⟨R, H, q0, a, b, hRV, hHT, hH, hqH, h0, hWin, hW, hGq⟩ := hHost s hs hxH hmem
  obtain ⟨c, hc, -⟩ := hCode s R hs hxC hRV
  have hHT' : H.CT2 = C.CT2 := hHT.trans hT.symm
  have hn : 0 < R.n := R.toFrame.ord_pos
  have hq0 : (q0 : ℝ) < s.X' := by
    have hqp : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    have hn' : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    exact hq s _ q0 hs hxq (by positivity) hH.1.log_cond_le hH.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  choose pt hsc hval har hfrom hcan hhas using
    fun i : Fin R.n => hObj s R H q0 a b _ c i.1 hs hxO hRV hHT' (by show HostGood s C.P.Cpde C5 c6 Cb H q0; rw [hP]; exact hH) hqH hWin rfl hc i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ?_⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩
  · have hd := DC.has_withDuty_wall_and_choices (C8 := C8) (c6 := c6) (q0 := q0) (pt i) hC hHT' (by rw [hsc i]; exact hH)
      (by rw [hsc i]; exact hq0) h0 (by rw [hsc i]; exact hW) (hval i) (hfrom i) (hcan i) (hhas i)
    exact ⟨⟨hd.1, G.at_of_from (hfrom i) (by rw [hsc i]; exact hGq)⟩, hd.2⟩

end UpperTheory.Top
end
end
