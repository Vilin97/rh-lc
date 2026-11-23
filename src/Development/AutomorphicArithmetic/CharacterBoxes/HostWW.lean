module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValid
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsWeightsInWindows

section

@[expose] public section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem exists_weights_in_windows : ∀ (eps : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → ∃ x0 : ℝ,
    ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R →
      ∃ a b : R.A → ℤ, WinOK s C.GK H a b := by
  intro eps C h0 h1 hS
  have hLa : 1 ≤ C.GK.La := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, hN⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hP⟩ := GlobalTheory.scale_poly_comparison eps 17 1 h0 one_pos
  obtain ⟨x3, hR⟩ := GlobalTheory.EX.rank_basic_bounds eps h0 h1
  refine ⟨max x1 (max x2 x3), fun s R H he hx hRV => ?_⟩
  have hx1 : x1 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, hK⟩ := hN s he hx1
  have hLa1 := (hK C.GK hLa).1
  obtain ⟨-, -, hb, -, hb', -⟩ := hP s he hx2
  obtain ⟨-, -, hr, hkr, -⟩ := hR s R he hx3 hRV
  have hx1' : 1 ≤ s.x := s.one_lt_alt.le
  have hxp : 0 < s.x := lt_of_lt_of_le one_pos hx1'
  have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hk0 : (0 : ℝ) < R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < R.k)
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  rw [Real.rpow_one] at hb
  rw [sub_self, Real.rpow_zero, one_mul] at hb'
  have h17 : 0 < s.x ^ (17 : ℝ) := Real.rpow_pos_of_pos hxp _
  have hb17 : s.x ^ (17 : ℝ) ≤ s.b := le_trans (le_mul_of_one_le_right h17.le hX) hb
  have hA : 1 ≤ s.a / ((R.k : ℝ) * s.x ^ (Scale.A / 2)) := by
    have h13 : 0 < s.x ^ (Scale.A / 2) := Real.rpow_pos_of_pos hxp _
    rw [le_div_iff₀ (mul_pos hk0 h13), one_mul]
    calc (R.k : ℝ) * s.x ^ (Scale.A / 2) ≤ s.x ^ (5 : ℝ) * s.x ^ (Scale.A / 2) :=
          mul_le_mul_of_nonneg_right hk5 h13.le
      _ = s.x * s.x ^ (17 : ℝ) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_one_add' hxp.le (by norm_num)]
          congr 1
          unfold Scale.A
          norm_num
      _ ≤ s.a := mul_le_mul_of_nonneg_left hb17 hxp.le
  have hB : 1 ≤ 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (R.k : ℝ) := by
    rw [le_div_iff₀ hk0, one_mul]
    have hn : (1 : ℝ) ≤ R.n := by
      have : 1 ≤ R.n := R.ord_pos
      exact_mod_cast this
    have hd : 1 ≤ s.delta1 * s.x ^ s.eps := by
      unfold Scale.delta1
      rw [← Real.rpow_add hxp]
      exact Real.one_le_rpow hx1' (by have := s.eps_pos; linarith)
    have hL : 1 ≤ G.La C.GK s := le_trans (Real.one_le_rpow hx1' s.eps_pos.le) hLa1
    have hkb : (R.k : ℝ) ≤ s.b' :=
      le_trans hk5 (le_trans (Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)) hb')
    have h2 : (1 : ℝ) ≤ 2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hd) hL
    calc (R.k : ℝ) ≤ s.b' := hkb
      _ ≤ (2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s) * s.b' :=
          le_mul_of_one_le_left (le_trans hk0.le hkb) h2
      _ = _ := by ring
  refine ⟨fun _ => ⌈s.a⌉, fun _ => ⌈s.b'⌉, fun t _ => ⟨⟨Int.le_ceil _, ?_⟩, Int.le_ceil _, ?_⟩⟩
  · have := Int.ceil_lt_add_one s.a
    linarith
  · have := Int.ceil_lt_add_one s.b'
    linarith

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem kit_of_points : ∀ (Q : PtProp) (C : FC) (cD ch : ℝ) (s : Scale) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool), (∀ u0 : ℕ, u0 < R.n → ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q) → ∃ k : Kit C cD ch s, ∀ i, (∃ u0, (k.pt i).From H a b c u0) ∧ CanonInst (k.pt i).ta.Gx ∧ (k.pt i).Has Q := by
  intro Q C cD ch s R H a b M c hObj
  have hn : 0 < R.n := by unfold Ranks.n; exact R.ord_pos
  choose pt hsc hval har hfrom hcan hhas using fun i : Fin R.n => hObj i.1 i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ⟨⟨i.1, hfrom i⟩, hcan i, hhas i⟩⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩

end GlobalTheory.EX.DC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

theorem weightWindowRequirement_host_of_point : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → Formalism.MainNotions.AuxBlock8.WeightVectorExists p.D p.L p.ta.Gx C.GK → ∃ a' b' : R.A → ℤ, (∀ t, t ∉ H.TT → a' t = 0 ∧ b' t = 0) ∧ WinOK p.L.sc C.GK H a' b' ∧ WOK p.L.sc cD ch C.GK H a' b' := by
  intro C cD ch p R H a b M c u0 _ hV hF hC hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, -, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  obtain ⟨a', ha, b', hb, hW⟩ := hW
  have ha' := Fintype.mem_piFinset.1 ha
  have hb' := Fintype.mem_piFinset.1 hb
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  refine ⟨a', b', fun t ht => ?_, fun t ht => ?_, ?_⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_false, Finset.mem_singleton] at h1 h2
    exact ⟨h1, h2⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_true, G.winA, G.winB, Finset.mem_Icc, Int.ceil_le, Int.le_floor, G.Nstar] at h1 h2
    exact ⟨h1, h2⟩
  · have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
        p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
        (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
         open Classical in
         ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
          (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l then (1 : ℝ) else 0) +
            4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) := by
      intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6
      obtain rfl : G.hP p.D = hf := funext e6
      subst e1 e2 e0 e3 e4 e5
      unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands at hW
      simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1] at hW
      exact hW
    exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh'

end GlobalTheory.EX

end
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.HostWW

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

private theorem gk_nonneg {C : FC} (h : Std C) : C.GK.Nonneg := by
  obtain ⟨⟨f1, f2, f3, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hm, hl⟩ := h
  have hm' : ∀ c ∈ C.cMid C.P.CF, 0 ≤ c := fun c hc => zero_le_one.trans (hm c hc)
  have hl' : ∀ c ∈ C.cLast, 0 ≤ c := fun c hc => zero_le_one.trans (hl c hc)
  refine ⟨hm' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_,
    by rw [f2]; norm_num, by rw [f3]; norm_num, by rw [f1]; norm_num, hl' _ ?_⟩ <;> simp [FC.cMid, FC.cLast]

private theorem large_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
   ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

private theorem scale_ext {s s' : Scale} (h1 : s.x = s'.x) (h2 : s.eps = s'.eps) (h3 : s.J = s'.J) : s = s' := by
  cases s; cases s'; simp_all

theorem UpperTheory.Top.hostWW :
    ∀ (Q : PtProp) (la : ℝ) (P : HostReq), 1 < la → DC.HostExQW la P → DC.ObjC Q → DC.WClosed → DC.HostWW la P := by
  rintro Q la P hla hH ⟨ε0, hε0, hO⟩ ⟨ε1, hε1, hW⟩
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps he hle he52 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, h5, h6, hb, S, hH⟩ := hH eps he he52
  obtain ⟨K0, hO⟩ := hO eps C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) he52 h8
  obtain ⟨K1, hW⟩ := hW eps he (hle.trans (min_le_right _ _))
  refine ⟨CT2, C8, C5, c6, Cb, K0.sup K1, h8, h5, h6, hb, fun C hStd hCT2 hCp hL => ?_⟩
  obtain ⟨hL0, hL1⟩ := large_sup hL
  obtain ⟨c1, hO⟩ := hO C hStd hCp hL0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hO⟩ := hO cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hN⟩ := hN cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hO⟩ := hO ch ((le_max_left _ _).trans hch)
  obtain ⟨xN, hN⟩ := hN ch ((le_max_right _ _).trans hch)
  have hmid := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCF : (0 : ℝ) ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hCG : (0 : ℝ) ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xw, hw⟩ := exists_weights_in_windows eps C he he52 hStd
  obtain ⟨xc, hc⟩ := exists_injective_words eps C.CGam C.P.CF he he52 hCG hCF
  obtain ⟨x1, hx1, a1, a2, a3, a5, a6⟩ : ∃ x1 : ℝ, 1 < x1 ∧ xH ≤ x1 ∧ xO ≤ x1 ∧ xN ≤ x1 ∧ xw ≤ x1 ∧ xc ≤ x1 :=
    ⟨max 2 (max xH (max xO (max xN (max xw xc)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  let G : Scale → Prop := fun s => ∃ (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ),
    RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ q0 = DC.q0H H ∧ (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) ∧
      WinOK s C.GK H a b ∧ WOK s cD ch C.GK H a b ∧ P C5 s R H q0
  let Q' : PtProp := fun D L _ Gx _ K _ _ _ => AuxBlock8.WeightVectorExists D L Gx K → G L.sc
  have hK : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q' := by
    intro s hs hx hm
    obtain ⟨R, H, q0, hRV, hHT, hHG, hq, hP⟩ := hH s hs (a1.trans hx) hm
    obtain ⟨a, b, hab⟩ := hw s R H hs (a5.trans hx) hRV
    obtain ⟨c, hci, -⟩ := hc s R hs (a6.trans hx) hRV
    obtain ⟨k, hk⟩ := DC.kit_of_points Q C cD ch s R H a b _ c fun u0 hu =>
      hO s R H q0 a b _ c u0 hs (a2.trans hx) hRV (hHT.trans hCT2.symm) hHG hq hab rfl hci hu
    refine ⟨k, fun i hp => ?_⟩
    obtain ⟨⟨u0, hF⟩, hI, -⟩ := hk i
    obtain ⟨a', b', e1, e2, e3⟩ := weightWindowRequirement_host_of_point C cD ch (k.pt i) R H a b _ c u0 hStd (k.val i) hF hI hp
    rw [k.sc_eq i] at e2 e3 ⊢
    exact ⟨R, H, q0, a', b', hRV, hHT, hHG, hq, e1, e2, e3, hP⟩
  choose k hk using hK
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) := by
    intro s h h' h'' i
    refine (hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)).1
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact a3.trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, -, hQ, -, hJ, hWin, -⟩ :=
    exists_famP_of_kits eps C cD ch x1 la S he he52 hx1 hla.le hStd (gk_nonneg hStd) k hnum
  have hFL : Fm.Large K1 C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hL1
  obtain ⟨xW, hW⟩ := hW Fm C.P.CF trivial hFL
  refine ⟨max (Fm.x1 + 1) xW, S, fun s hs hx hm => ?_⟩
  have hx' : Fm.x1 < s.x := by have := (le_max_left _ _).trans hx; linarith
  obtain ⟨i⟩ := Fm.Ix_win s.x (by rw [hWin]; exact hm.2)
  have hG : G (Fm.L s.x i).sc := hQ Q' hk s.x hx' i (hW s.x ((le_max_right _ _).trans hx) i)
  have e : (Fm.L s.x i).sc = s :=
    scale_ext (Fm.L_x _ i hx') ((Fm.L_eps _ i).trans hs.symm) ((Fm.L_J _ i).trans (hJ.trans hm.1.symm))
  rw [e] at hG
  exact hG
end
end
