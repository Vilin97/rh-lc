module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FnValLift
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.ArelStar

section

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBH

section core

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem rel_inv {a b : Pr V} {a' b' : Pr V'} (h : Rel T a a') (hab : a * b = 1) (hba : b * a = 1)
    (hab' : a' * b' = 1) (hba' : b' * a' = 1) : Rel T b b' := by
  have e1 : a.1 * b.1 = 1 := congrArg Prod.fst hab
  have e2 : b'.1 * a'.1 = 1 := congrArg Prod.fst hba'
  have e3 : a.2.unop * b.2.unop = 1 := congrArg (fun x : Pr V => x.2.unop) hba
  have e4 : b'.2.unop * a'.2.unop = 1 := congrArg (fun x : Pr V' => x.2.unop) hab'
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have i1 : a.1 (b.1 v) = v := by simpa using LinearMap.congr_fun e1 v
    have i2 : b'.1 (a'.1 (T (b.1 v))) = T (b.1 v) := by simpa using LinearMap.congr_fun e2 (T (b.1 v))
    have i3 : a'.1 (T (b.1 v)) = T (a.1 (b.1 v)) := LinearMap.congr_fun h.1 (b.1 v)
    show b'.1 (T v) = T (b.1 v)
    rw [← i2, i3, i1]
  · have i1 : a.2.unop (b.2.unop v) = v := by simpa using LinearMap.congr_fun e3 v
    have i2 : b'.2.unop (a'.2.unop (T (b.2.unop v))) = T (b.2.unop v) := by
      simpa using LinearMap.congr_fun e4 (T (b.2.unop v))
    have i3 : a'.2.unop (T (b.2.unop v)) = T (a.2.unop (b.2.unop v)) := LinearMap.congr_fun h.2 (b.2.unop v)
    show b'.2.unop (T v) = T (b.2.unop v)
    rw [← i2, i3, i1]

theorem arel_star' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ARel T (star M) (star M') :=
  fun x y => by
    rw [Matrix.star_apply, Matrix.star_apply]
    exact rel_star (h y x)

theorem arel_pow' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ∀ n : ℕ, ARel T (M ^ n) (M' ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact arel_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact arel_mul (arel_pow' h n) h

theorem brel_of {a b c d : SlopeTestRemainingChoices S (Pr V)} {a' b' c' d' : SlopeTestRemainingChoices S (Pr V')} (h1 : ARel T a a') (h2 : ARel T b b')
    (h3 : ARel T c c') (h4 : ARel T d d') : BRel T !![a, b; c, d] !![a', b'; c', d'] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h4

structure Gen {r₀ r₁ : ℕ} (T : V →ₗ[ℂ] V') (L₀ : LevelData (Pr V) r₀) (L : LevelData (Pr V') r₁) : Prop where
  ζ : Rel T L₀.ζ L.ζ
  ζi : Rel T L₀.ζi L.ζi
  ζb : Rel T L₀.ζb L.ζb
  ζbi : Rel T L₀.ζbi L.ζbi
  GG : Rel T L₀.GG L.GG
  GGi : Rel T L₀.GGi L.GGi
  TT : L₀.TT = L.TT

abbrev Corr (T : V →ₗ[ℂ] V') (inv0 : Set ℂ) (f₀ : FrameData S (Pr V)) (f : FrameData S (Pr V')) : Prop :=
  ARel T f₀.F f.F ∧ ARel T f₀.Fi f.Fi ∧ ARel T f₀.c f.c ∧ ARel T f₀.ci f.ci ∧ (∀ Y, ARel T (f₀.x Y) (f.x Y)) ∧
    (∀ Y ∈ inv0, ARel T (f₀.xi Y) (f.xi Y)) ∧ (∀ Y, BRel T (f₀.TT Y) (f.TT Y)) ∧ f₀.N = f.N ∧ f₀.q = f.q ∧
    f₀.inv = f.inv ∧ f₀.inv ⊆ inv0

variable {r₀ r₁ : ℕ} {L₀ : LevelData (Pr V) r₀} {L : LevelData (Pr V') r₁}

theorem l_eq {r : ℕ} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (L : LevelData A r) (f : FrameData S A)
    (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) :
    f.l L Y = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by
  have h := hf.frame_l Y hY hY1
  have hio : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by simp only [io, ← map_mul, L.GGi_GG, map_one]
  have hx := (hf.x_xi Y hY).2
  calc f.l L Y = (f.xi Y * f.x Y) * f.l L Y * (f.F * f.Fi) := by rw [hx, hf.F_Fi, one_mul, mul_one]
    _ = f.xi Y * ((io L.GGi * io L.GG) * f.x Y * f.l L Y * f.F) * f.Fi := by
      rw [hio]; simp only [one_mul, mul_assoc]
    _ = f.xi Y * io L.GGi * (io L.GG * f.x Y * f.l L Y * f.F) * f.Fi := by simp only [mul_assoc]
    _ = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by rw [← h]; simp only [mul_assoc]

theorem l_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f₀.inv)
    (hY1 : Y + 1 ∈ f₀.inv) : ARel T (f₀.l L₀ Y) (f.l L Y) := by
  obtain ⟨hF, hFi, -, -, -, hxi, hTT, -, -, hinv, hsub⟩ := hc
  rw [l_eq L₀ f₀ hf₀ Y hY hY1, l_eq L f hf Y (hinv ▸ hY) (hinv ▸ hY1)]
  exact arel_mul (arel_mul (arel_mul (arel_mul (hxi Y (hsub hY)) (arel_io G.GGi)) hF) (hTT Y 1 0)) hFi

theorem m_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y - 1 ∈ f₀.inv)
    (hY1 : Y ∈ f₀.inv) : ARel T (f₀.m L₀ Y) (f.m L Y) := by
  have hl := l_rel G hc hf₀ hf (Y - 1) hY (by rw [sub_add_cancel]; exact hY1)
  obtain ⟨-, -, hc', hci, -, -, -, hN, -, -, -⟩ := hc
  have hwt : ARel T (wt (S := S) L₀) (wt L) := arel_io (rel_mul (rel_mul G.ζ G.ζb) G.GGi)
  have hwti : ARel T (wti (S := S) L₀) (wti L) := arel_io (rel_mul (rel_mul G.GG G.ζi) G.ζbi)
  unfold FrameData.m FrameData.d FrameData.di
  rw [hN]
  exact arel_mul (arel_mul (arel_mul hci (arel_pow' hwti _)) (arel_star' hl)) (arel_mul (arel_pow' hwt _) hc')

theorem corr_plus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (a : S) (Ya : ℂ) (h1 : Ya ∈ f₀.inv)
    (h2 : Ya + 1 ∈ f₀.inv) : Corr T inv0 (f₀.plus L₀ a Ya) (f.plus L a Ya) := by
  have hl := l_rel G hc hf₀ hf Ya h1 h2
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.plus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins a (brel_mul (brel_of (arel_io G.ζi) arel_zero arel_zero (arel_io G.ζbi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hl) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins a (brel_mul (brel_of arel_one arel_zero (arel_neg hl) (arel_io G.GGi))
      (brel_of (arel_io G.ζ) arel_zero arel_zero (arel_io G.ζb))))
  · rw [hq]
    exact arel_mul hc' (arel_ins a (brel_of (arel_smul _ (hxi _ (hsub h2))) arel_zero arel_zero (hx Ya)))
  · rw [hq]
    exact arel_mul hci (arel_ins a (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (hTT Y) (block_relation_height a _)

theorem corr_minus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (b : S) (Yb : ℂ) (h1 : Yb ∈ f₀.inv)
    (h0 : Yb - 1 ∈ f₀.inv) : Corr T inv0 (f₀.minus L₀ b Yb) (f.minus L b Yb) := by
  have hm := m_rel G hc hf₀ hf Yb h0 h1
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.minus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins b (brel_mul (brel_of (arel_io G.ζbi) arel_zero arel_zero (arel_io G.ζi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hm) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins b (brel_mul (brel_of arel_one arel_zero (arel_neg hm) (arel_io G.GGi))
      (brel_of (arel_io G.ζb) arel_zero arel_zero (arel_io G.ζ))))
  · rw [hq]
    exact arel_mul hc' (arel_ins b (brel_of (arel_smul _ (hxi _ (hsub h0))) arel_zero arel_zero (hx Yb)))
  · rw [hq]
    exact arel_mul hci (arel_ins b (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (block_relation_twisted_height b _) (hTT Y)

variable {st₀ : Start (Pr V)} {st : Start (Pr V')}

theorem x_rel (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (Y : ℂ) : Rel T (st₀.x Y) (st.x Y) := by
  have e₀ : st₀.x Y = L₀.GGi * st₀.QQ Y 1 1 := by rw [hs₀.tau, ← mul_assoc, L₀.GGi_GG, one_mul]
  have e : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hs.tau, ← mul_assoc, L.GGi_GG, one_mul]
  rw [e₀, e]
  exact rel_mul G.GGi (hQ Y 1 1)

theorem corr_word (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) :
    ∀ w : List (Letter ℂ S), AdmRec L₀ st₀ w → AdmRec L st w →
      Corr T st₀.inv (ofWord L₀ st₀ w) (ofWord L st w) := by
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨arel_one, arel_one, arel_one, arel_one, fun Y => arel_io (x_rel G hQ hs₀ hs Y), fun Y hY => ?_,
      fun Y => brel_lift0 (hQ Y), rfl, hq, hinv, subset_rfl⟩
    exact arel_io (rel_inv (x_rel G hQ hs₀ hs Y) (hs₀.x_xi Y hY).1 (hs₀.x_xi Y hY).2
      (hs.x_xi Y (hinv ▸ hY)).1 (hs.x_xi Y (hinv ▸ hY)).2)
  | cons l w ih =>
    intro h₀ h
    unfold AdmRec at h₀ h
    obtain ⟨hw₀, -, -, hp0, hp1, hrest⟩ := h₀
    obtain ⟨hw, -⟩ := h
    have hf₀ := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V) S r₀ L₀ st₀ w hL₀ hs₀ hw₀
    have hf := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V') S r₁ L st w hL hs hw
    by_cases hp : l.plus
    · simpa only [ofWord, ite_eq_left hp] using
        corr_plus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hp1
    · rw [ite_eq_right hp] at hrest
      simpa only [ofWord, ite_eq_right hp] using
        corr_minus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hrest.1

theorem act_frame (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (w : List (Letter ℂ S)) (h₀ : admitted st₀ w) (h : admitted st w) (Ψ : Ix S → V) (e : Ix S) :
    T (∑ b, ((ofWord L₀ st₀ w).F e b).1 (Ψ b)) = ∑ b, ((ofWord L st w).F e b).1 (T (Ψ b)) :=
  act_tr (corr_word G hQ hq hinv hL₀ hL hs₀ hs w
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V) S r₀ L₀ st₀ w h₀)
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V') S r₁ L st w h)).1 Ψ e

end core

end Formalism.FourierDecayAlt.P.WordCorrespondence
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransportToLastLevel

section

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem transport_gen {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    (hz : D.castV hn (liftVec k i r' zs) = z) (hz' : D.castV hn (liftVec k i r' zs') = z')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)} {πs : Mx k r' → (Wp →L[ℂ] Wp)}
    {πs' : Mx k r' → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k i r' y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k i r' y)))
    (X₀ : ActualOps k n z z' π π') (L₀ : R.LevelData (Pr (RadSp k n z z' π π')) n)
    (st₀ : Fr.Start (Pr (RadSp k n z z' π π')))
    (X : ActualOps k r' zs zs' πs πs') (L : R.LevelData (Pr (RadSp k r' zs zs' πs πs')) r')
    (st : Fr.Start (Pr (RadSp k r' zs zs' πs πs')))
    (hL₀ : IsActualLevel X₀ L₀) (hL : IsActualLevel X L) (s : ℂ) (hst₀ : ∀ Y, st₀.QQ Y = s • X₀.QQ Y)
    (hst : ∀ Y, st.QQ Y = s • X.QQ Y) (hq : st₀.q = st.q) (hinv : st₀.inv = st.inv)
    (hSL₀ : Fr.IsStarLevel L₀) (hSL : Fr.IsStarLevel L) (hs₀ : Fr.IsLevelStart L₀ st₀) (hs : Fr.IsLevelStart L st)
    (c : Fin n → ℂ) (hc : c ∈ OmX n) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k r' zs zs' πs πs',
      (∀ Ψ c' g, (T Ψ : Fn k r' (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → RadSp k n z z' π π') (e : Wd.Ix (Fin w.length)) (c' : Fin r' → ℂ)
        (g : B.Mat k r'),
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e : Fn k r' (Wq →L[ℂ] Wp)) c' g := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k i r' y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k i r' y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  have fr := fun (j : Fin 6) v => fn_rs hr' hc X₀ X j v
  have tr := fun Y (a b : Fin 2) v => t_rs hr' hc X₀ X Y a b v
  obtain ⟨-, -, -, -, -, -, h0ζ, h0ζi, h0ζb, h0ζbi, h0G, h0Gi, h0TT⟩ := hL₀
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hG, hGi, hTT⟩ := hL
  have G : Gen (rsL hr' hc zs zs' π π') L₀ L :=
    { ζ := by rw [h0ζ, hζ]; exact rel_mk (fr 0) (fr 2)
      ζi := by rw [h0ζi, hζi]; exact rel_mk (fr 1) (fr 3)
      ζb := by rw [h0ζb, hζb]; exact rel_mk (fr 2) (fr 0)
      ζbi := by rw [h0ζbi, hζbi]; exact rel_mk (fr 3) (fr 1)
      GG := by rw [h0G, hG]; exact rel_mk (fr 4) (fr 4)
      GGi := by rw [h0Gi, hGi]; exact rel_mk (fr 5) (fr 5)
      TT := by rw [h0TT, hTT, tz_lift, tz_lift] }
  have hQ : ∀ Y, MRel (rsL hr' hc zs zs' π π') (st₀.QQ Y) (st.QQ Y) := fun Y => by
    rw [hst₀, hst]
    exact mrel_smul s fun a b => rel_mk (fun v => tr Y a b v) (fun v => tr (star Y) b a v)
  refine ⟨rsL hr' hc zs zs' π π', fun Ψ c' g => by rw [P.JCTx5.castM_rfl]; rfl, fun w h₀ h Ψ e c' g => ?_⟩
  rw [P.JCTx5.castM_rfl]
  have key := act_frame G hQ hq hinv hSL₀ hSL hs₀ hs (D.positionted w) h₀ h Ψ e
  exact congrArg (fun v : RadSp k r' zs zs' _ _ => (v : Fn k r' (Wq →L[ℂ] Wp)) c' g) key

end Formalism.FourierDecayAlt.P.WordCorrespondence

theorem Formalism.FourierDecayAlt.P.frame_transport_to_last_level : Formalism.FourierDecayAlt.P.PBI.FrameTransport := by
  intro Wp Wq _ _ _ _ _ _ P p X₀ μ₀ L₀ st₀ X μ L st hD₀ hD c hc
  obtain ⟨T, hT, hact⟩ := Formalism.FourierDecayAlt.P.WordCorrespondence.transport_gen P.k P.r P.r (P.r - P.r) (by omega) (by omega)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    X₀ L₀ st₀ X L st hD₀.2.2.1 hD.2.2.1 (Formalism.FourierDecayAlt.M.sgn P p.l0) hD₀.2.2.2.1 hD.2.2.2.1
    (hD₀.2.2.2.2.1.trans hD.2.2.2.2.1.symm) (hD₀.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm)
    hD₀.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.1 hD₀.2.2.2.2.2.2.2 hD.2.2.2.2.2.2.2 c hc
  exact ⟨T, hT, fun w h₀ h Ψ e c' g _ _ => hact w h₀ h Ψ e c' g⟩
end
end
end
