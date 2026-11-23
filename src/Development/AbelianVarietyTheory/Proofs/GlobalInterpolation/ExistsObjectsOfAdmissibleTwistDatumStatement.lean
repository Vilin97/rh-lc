module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLedPart
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitConstantsParameterConditionsLarge
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InjectiveOfOrder
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ObjCOfRecExObjO

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB.Bridge

theorem exists_T_of_over {D : D7} {P : PreCh} {Lv : LevCh P} (h : Over D P Lv) (u : D.what₂.Word) :
    ∃ u', (D.mem u).A.T = Lv.T u' := by
  obtain ⟨sp, hT, hY, hA, hV, hz, X, h1, rfl⟩ := h
  have key : ∀ B : Pre, B = Pre.ofCh P Lv sp hT hY hA hV hz → ∀ v : B.Word, ∃ u', B.T v = Lv.T u' := by
    rintro B rfl v
    exact ⟨v, rfl⟩
  obtain ⟨u', hu⟩ := key X.B.toPre h1 u
  exact ⟨u', (X.C.A_T u).trans hu⟩

theorem scale_X'_le_of_log (eps cs : ℝ) (he : 0 < eps) (hc : 0 < cs) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (T : ℝ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 0 < T → cs * R.m * s.L ≤ Real.log T → s.X' ≤ T := by
  refine ⟨cs⁻¹ ^ ((2 * eps / 3)⁻¹), fun s R T hs hx hR hT h => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hm : (1 : ℝ) ≤ R.m := by
    refine le_trans ?_ hR.2.1.1
    rw [Real.one_le_sqrt, Scale.delta1, ← Real.rpow_one_add' hx0.le (by linarith)]
    exact Real.one_le_rpow hx1.le (by linarith)
  have h1 : cs⁻¹ ≤ s.x ^ (2 * eps / 3) := by
    have := Real.rpow_le_rpow (by positivity) hx (show 0 ≤ 2 * eps / 3 by positivity)
    rwa [Real.rpow_inv_rpow (by positivity) (by positivity)] at this
  have h2 : s.L = s.x ^ (2 * eps / 3) * s.x ^ (s.eps / 3) := by
    rw [Scale.L, ← Real.rpow_add hx0, hs]; congr 1; ring
  have h3 : 1 ≤ cs * s.x ^ (2 * eps / 3) := by
    have := mul_le_mul_of_nonneg_left h1 hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at this
  have h4 : 0 < s.x ^ (s.eps / 3) := by positivity
  have h5 : s.x ^ (s.eps / 3) ≤ cs * R.m * s.L := by
    have : cs * R.m * s.L = (cs * s.x ^ (2 * eps / 3) * R.m) * s.x ^ (s.eps / 3) := by rw [h2]; ring
    rw [this]
    exact le_mul_of_one_le_left h4.le (one_le_mul_of_one_le_of_one_le h3 hm)
  rw [Scale.X', ← Real.le_log_iff_exp_le hT]
  exact h5.trans h

theorem scale_one_le_w'' (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 1 ≤ s.w'' R.n := by
  obtain ⟨x0, h⟩ := GlobalTheory.scale_poly_comparison eps 0 1 he one_pos
  refine ⟨max x0 4, fun s R hs hx hR => ?_⟩
  have hx4 : 4 ≤ s.x := (le_max_right _ _).trans hx
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hn : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have h2 : (2 : ℝ) ≤ s.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have h3 : (R.n : ℝ) ≤ s.x ^ (3 : ℝ) := by
    have a1 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have a2 : s.x ^ (3 : ℝ) = s.x ^ ((1 : ℝ) / 2) * s.x ^ ((5 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [a2]
    exact hR.1.2.trans (mul_le_mul h2 a1 (by positivity) (by positivity))
  have := ((h s hs ((le_max_left _ _).trans hx)).2.2.2.2.2.1 R.n hn h3).1
  simpa using this

end GlobalTheory.EX.OB.Bridge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsParametersOver

section

@[expose] public section

noncomputable section

namespace GlobalTheory.EX.OB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField



theorem exists_sizeData_over : ∀ (eps cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P) (D : D7), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R → Over D P Lv → RecOK s C cD D → HostArith D.host ∧ (∃ L : SizeData₂ D, L.sc = s ∧ WtEq L a b ∧ Val C cD ch L) ∧ D.R = P.R ∧ D.host.TT.image Formalism.HC.Frame.A.val = P.H.TT.image Formalism.HC.Frame.A.val ∧ D.host.T2 = P.H.T2 ∧ D.host.q = P.H.q ∧ D.host.d = P.H.d ∧ D.host.g = P.H.g ∧ D.host.pde = P.H.pde ∧ D.host.pde' = P.H.pde' ∧ P.H.levelPrimes ⊆ D.host.levelPrimes ∧ D.host.u0.val = P.H.u0.val ∧ (∀ l, (G.hP D l).val = (hPH P.H l).val) ∧ ∃ eW : D.what₂.Word ≃ P.Word, ∀ u l, wordBits D u l = if h : l < P.R.k - 2 then c (eW u) ⟨l, h⟩ else false := by
  intro eps cD ch C h0 h1 hC hcD hch
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv D hs hx hP hG hO hR
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hB, rfl⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (Pre.ofCh P Lv sp hT hY hA hV hz).level_split
  refine ⟨⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Finset.subset_union_left, rfl, fun l => rfl, Equiv.refl _, ?_⟩
  · obtain ⟨L, e1, e2, e3, e4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog hR.del hP.ct2
      hP.card hR.etaF (fun u => by
        have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
        rw [e, hG, GamS, Real.log_exp]; rfl)
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) hR.untw
    refine ⟨L, e1, ?_, e4⟩
    intro t t' htt
    have : t.1 = t' := Formalism.HC.Frame.A.val_injective _ htt
    rw [e2, e3]
    subst this
    exact ⟨rfl, rfl⟩
  · intro u l
    unfold wordBits
    by_cases h : l < P.R.k - 2
    · have h' : l < D.R.k - 2 := h
      rw [dite_eq_left h', dite_eq_left h]
      have τ : Tau P.R := tauPl D (false, 0)
      have a1 := D.s.u_letter u τ l h'
      have a2 := hP.code u τ l h
      have a3 := a1.symm.trans a2
      have hpos := D.s.Del_pos
      rw [← hR.del] at a3
      show D.s.letter u ⟨l, h'⟩ = c u ⟨l, h⟩
      have a4 : (if D.s.letter u ⟨l, h'⟩ = true then D.s.Del else 0) = (if c u ⟨l, h⟩ = true then D.s.Del else 0) :=
        sub_right_injective a3
      revert a4
      cases D.s.letter u ⟨l, h'⟩ <;> cases c u ⟨l, h⟩ <;> simp [hpos.ne', hpos.ne]
    · have h' : ¬ l < D.R.k - 2 := h
      rw [dite_eq_right h', dite_eq_right h]

end GlobalTheory.EX.OB

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.Fc

theorem ObjCP.imp {Q Q' : Par → PtProp} (h : ObjCP Q) (hi : ∀ (κ : Par) (p : Pt κ.C), p.Has (Q κ) → p.Has (Q' κ)) : ObjCP Q' :=
  ParEv.mono (fun κ ⟨x0, H⟩ => ⟨x0, fun s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 =>
    let ⟨p, e1, e2, e3, e4, e5, e6⟩ := H s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9
    ⟨p, e1, e2, e3, e4, e5, hi κ p e6⟩⟩) h


open GlobalTheory.EX.DC in
theorem ObjCP.and_q0Pt {Q : Par → PtProp} (h : ObjCP Q) : ObjCP (fun κ => (Q κ).and twistingGlobalPointProp) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  obtain ⟨c1', hP⟩ := explicitConstants_parameterConditions_large eps a1 a3 C b1
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hP⟩ := hP cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch ((le_max_left _ _).trans hch)
  obtain ⟨x1, hP⟩ := hP ch ((le_max_right _ _).trans hch)
  obtain ⟨x2, hq⟩ := small_prime_lt eps C8 a1 a4
  obtain ⟨x3, hJ⟩ := GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1
  refine ⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  dsimp only at d1 d4 d5 d6 d7
  rw [b2] at d5
  simp only [max_le_iff] at d2
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 (b2 ▸ d5) d0 d6 d7 d8 d9
  refine ⟨p, e1, e2, e3, e4, e5, e6, ?_⟩
  dsimp only at e2 p
  subst e1
  show GlobalTwistingFacts p.L
  obtain ⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩ := d5
  have eq0 : q0Av p.D = q0 := (eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm
  have hX : (q0Av p.D : ℝ) < p.L.sc.X' := by
    rw [eq0]
    exact hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle
  obtain ⟨P, -⟩ := hP _ _ d1 d2.1.2 e2 e3
  have hXb := X'_le_b p.L.sc
  have hs := globalTwisting_spec_fact p.D.host
  have hg : ∀ j, q0Av p.D < p.D.host.g j := by
    intro j
    have hg := (e2.host.2.2.2.2.1 j).1
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast (show (q0Av p.D : ℝ) < p.D.host.g j by linarith)
  refine ⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2,
    fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩
  · rw [eq0]
    exact e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)
  · rw [Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]
    exact hX.le.trans hXb


open GlobalTheory.EX.DC GlobalTheory.EX.OB.Bridge in
theorem objCP_and_of_recExP (QO : Par → ∀ D : D7, Obj D → Prop) (hLP : LevelPrime) (hRec : RecExP QO) :
    ObjCP (fun κ => (ptO (QO κ)).and (TamePt.and (MinkPt.and TwPt))) := by
  obtain ⟨ε0, h0, hRec⟩ := hRec
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb e1 e2 e3 e4 => ?_⟩
  obtain ⟨K0, hRec⟩ := hRec eps C8 C5 c6 Cb e1 e2 e3 e4
  refine ⟨⟨K0.pre, K0.t, fun l => max (K0.mid l) 10, K0.last⟩, fun C hS hC8 hL => ?_⟩
  have hL0 : C.Large K0 C.P.CF :=
    ⟨hL.1, trivial, fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), hL.2.2.2⟩
  have hg : 10 ≤ C.cX.err.g := (le_max_right _ _).trans (hL.2.2.1 _ (by simp [FC.cMid]))
  obtain ⟨c1, hRec⟩ := hRec C hS hC8 hL0
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  have hcD0 : 0 ≤ cD := (le_max_right _ _).trans hcD
  obtain ⟨c2, hRec⟩ := hRec cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  have hch0 : 402 ≤ ch := (le_max_right _ _).trans hch
  obtain ⟨cs, x1, hcs, hRec⟩ := hRec ch ((le_max_left _ _).trans hch)
  obtain ⟨x2, h2⟩ := chGood_of_host eps C5 c6 Cb cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps cs C e1 e3 hcs hS
  obtain ⟨x4, h4⟩ := exists_sizeData_over eps cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x5, h5⟩ := scale_X'_le_of_log eps cs e1 hcs
  obtain ⟨x6, h6⟩ := scale_one_le_w'' eps e1
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 x6), ?_⟩
  intro s R H q0 a b M c u0 hs hx hR hCT hH hq0 hW hM hc hu
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨y1, y2⟩, y3, y4⟩, y5, y6⟩ := hx
  dsimp only at hs hCT hH hW hM
  rw [hq0] at hH
  obtain ⟨hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh⟩ := h2 s R H a b M c u0 hs y2 hR hCT hH hW hM hc
  obtain ⟨du, Ds, hdu, hDs, hlog, hRec⟩ := hRec s _ _ _ _ hs y1 hCh
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ _ _ _ _ du Ds hs y3 hCh.ok hdu hDs hlog
  obtain ⟨D, Y, hO, hRO, hLO, hTW, hQ⟩ := hRec Lv l1 l2 l3
  obtain ⟨hA, ⟨L0, m1, m2, m3⟩, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, eW, g11⟩ :=
    h4 s _ _ _ _ _ Lv D hs y4 hCh.ok l3 hO hRO
  have hDR : D.R = R := g0
  have hT : ∀ u, s.X' ≤ ((D.mem u).A.T : ℝ) := by
    intro u
    obtain ⟨u', hu'⟩ := exists_T_of_over hO u
    have w := (Lv.T_win u').1
    rw [l1, l2, l3] at w
    rw [hu']
    refine le_trans (h5 s R _ hs y5 hR ?_ (hlog u')) w
    have : (0 : ℝ) < du u' := by exact_mod_cast hdu u'
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  obtain ⟨p, n1, n2, n3, n4⟩ := Led.exists_ledPart C cD ch s D Y R.toFrame a b L0 hS hg (by rw [hDR]) m1 m2 m3 hA
    (by rw [hDR]; exact h6 s R hs y6 hR) hT hRO hLO
  exact ⟨p.pt, n1, p.pt_val n3, hA,
    ⟨hDR, g1, g2, g3, g4, g5, g6, g7, g8, g9.trans (R.toFrame.val_ofNat_of_lt hu), g10, p.pt_wtEq n2, ⟨eW, g11⟩,
      hO.field⟩, p.pt_canon n4,
    hQ p n1 n2 n3 n4, hRO.tame, hRO.mink, twAt_tr (nPrime p.L) p.ht hTW⟩

theorem objCP_of_recExP : ∀ QO : Par → ∀ D : D7, Obj D → Prop,
    LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) :=
  fun QO hL hR => (objCP_and_of_recExP QO hL hR).and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩

end GlobalTheory.Fc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.existsObjects_of_admissibleTwistDatum : ∀ QO : Par → ∀ D : D7, Obj D → Prop, LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) := by
  first | exact @GlobalTheory.Fc.objCP_of_recExP | exact GlobalTheory.Fc.objCP_of_recExP | (intros; apply GlobalTheory.Fc.objCP_of_recExP <;> assumption)
end
end
