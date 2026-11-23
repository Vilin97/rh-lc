module

public import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPtrueHom
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.CoeUntopDLeAlt
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.LeadingDepthOneMemClosure
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.LetterWeightPos
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EDelApply
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EvensBeforePairwise
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ExistsPolFamilyOfMemGenOfVsDegLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.GrowthBounds.ScaleEdges.MultidegreeBoundLeA

section

@[expose] public section

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem num_E (c' r k Q N₁ : ℕ) (hk : k ≤ c') (hN : N₁ ≤ k) (hN1 : 1 ≤ N₁) (hr : 2 ≤ r) (hQ : 3 ≤ Q) :
    (c' * (1 + r * k * Q) + c') * Q + (N₁ + 1) * (((2 * Q + 3) * c' + k * Q) * (r * Q)) ≤
      15 * c' * (N₁ + r * k) * Q ^ 2 := by
  have h1 : (2 * Q + 3) * c' + k * Q ≤ 4 * Q * c' := by
    nlinarith [Nat.mul_le_mul_right Q hk, Nat.mul_le_mul_right c' hQ]
  have h2 : N₁ + 1 ≤ 2 * k := by omega
  have h3 : (N₁ + 1) * (((2 * Q + 3) * c' + k * Q) * (r * Q)) ≤ (2 * k) * ((4 * Q * c') * (r * Q)) :=
    Nat.mul_le_mul h2 (Nat.mul_le_mul_right _ h1)
  have h5 : 2 ≤ r * k * Q := by
    calc 2 = 2 * 1 * 1 := by norm_num
      _ ≤ r * k * Q := Nat.mul_le_mul (Nat.mul_le_mul hr (by omega)) (by omega)
  have h4 : (c' * (1 + r * k * Q) + c') * Q ≤ 2 * (c' * (r * k) * Q ^ 2) := by
    have e : (c' * (1 + r * k * Q) + c') * Q = c' * Q * 2 + c' * Q * (r * k * Q) := by ring
    have e2 : 2 * (c' * (r * k) * Q ^ 2) = c' * Q * (r * k * Q) + c' * Q * (r * k * Q) := by ring
    rw [e, e2]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h5) _
  have e3 : (2 * k) * ((4 * Q * c') * (r * Q)) = 8 * (c' * (r * k) * Q ^ 2) := by ring
  have e4 : 15 * c' * (N₁ + r * k) * Q ^ 2 = 15 * (c' * N₁ * Q ^ 2) + 15 * (c' * (r * k) * Q ^ 2) := by ring
  rw [e3] at h3
  rw [e4]
  omega

theorem multidegree_bound_le_a (C k r N Q c' Y a N₁ : ℝ) (hC : 30 ≤ C) (hk : 1 ≤ k) (hr : 2 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hc : 0 ≤ c') (hY : 1 ≤ Y) (hN1 : N₁ ≤ k) (h : C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y ≤ a) :
    15 * c' * (N₁ + r * k) * Q ^ 2 ≤ a := by
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have hr2 : r ≤ r ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hQ5 : Q ^ 2 ≤ Q ^ 5 := pow_le_pow_right₀ hQ (by norm_num)
  have hQ2 : 0 ≤ Q ^ 2 := by positivity
  have h1 : N₁ + r * k ≤ 2 * (r * k) := by nlinarith
  have h2 : 15 * c' * (N₁ + r * k) * Q ^ 2 ≤ 15 * c' * (2 * (r * k)) * Q ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hQ2
  have a1 : 30 * k ≤ C * k ^ 3 := mul_le_mul hC hk3 (by linarith) (by linarith)
  have a2 : 30 * k * r ≤ C * k ^ 3 * r ^ 2 := mul_le_mul a1 hr2 (by linarith) (by positivity)
  have a3 : 30 * k * r ≤ C * k ^ 3 * r ^ 2 * N := le_trans a2 (le_mul_of_one_le_right (by positivity) hN)
  have a4 : 30 * k * r * Q ^ 2 ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 := mul_le_mul a3 hQ5 hQ2 (by positivity)
  have a5 : 30 * k * r * Q ^ 2 * c' ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' := mul_le_mul_of_nonneg_right a4 hc
  have a6 : 30 * k * r * Q ^ 2 * c' ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y :=
    le_trans a5 (le_mul_of_one_le_right (by positivity) hY)
  have e : 15 * c' * (2 * (r * k)) * Q ^ 2 = 30 * k * r * Q ^ 2 * c' := by ring
  linarith

theorem spdeg {C : ℝ} (hC : 30 ≤ C) {p n' m r : ℕ} [Fact p.Prime] [NeZero n'] {TT : Finset (Fin n')} {L₁ L₂ : ℕ}
    {de h x : ℝ} {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar)
    {F : Frames n' r} (hF : FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F) (t : Fin n') (ht : t ∈ F.TT) :
    eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤
        E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
      eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤ flatDeg lam0 t := by
  have hB := hyps_basic (C := C) (by linarith) H
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := H
  have hTT := hF.1
  have hGn : goodG' r de h x ≤ n' := by have := h3.2.2.2; omega
  have hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) (goodG' r de h x) (orbitWindowCount r de h x) := by
    rw [hTT]
    exact h3.1.2.2
  have hG1 : 1 ≤ goodG' r de h x := le_trans hB.one_le_depth_alt hB.depth_le_good_exponent
  have hpR : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
  have hkR : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h2
  have hNR : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hQR : (p : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := le_self_pow₀ (by linarith) (by omega)
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := by linarith
  have hcR : (8 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h8' : (8 : ℝ) ≤ (cStar : ℝ) := by
      have : 8 ≤ cStar := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  have sq_level_le_degree : orbitWindowCount r de h x ≤ m + 1 := by omega
  have hE0a : ((E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) : ℕ) : ℝ) ≤ a := by
    have := multidegree_bound_le_a C ((m + 1 : ℕ) : ℝ) r TT.card ((p : ℝ) ^ goodG' r de h x)
      ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) Y a (orbitWindowCount r de h x : ℝ) hC hkR hrR hNR hQ1
      (by linarith) (by linarith [hB.two_le_Y]) (by exact_mod_cast sq_level_le_degree) h12
    refine le_trans (le_of_eq ?_) this
    unfold E0 cPrime
    push_cast
    ring

  have hpa : (p : ℝ) ≤ a := by
    have hE : (p : ℝ) ≤ 15 * ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) *
        ((orbitWindowCount r de h x : ℝ) + r * ((m + 1 : ℕ) : ℝ)) * ((p : ℝ) ^ goodG' r de h x) ^ 2 := by
      have b1 : (1 : ℝ) ≤ 15 * ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) := by linarith
      have b2 : (1 : ℝ) ≤ (orbitWindowCount r de h x : ℝ) + r * ((m + 1 : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ (orbitWindowCount r de h x : ℝ) := Nat.cast_nonneg _
        nlinarith
      have b3 : (p : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 2 := le_trans hQR (le_self_pow₀ hQ1 (by norm_num))
      have b4 := one_le_mul_of_one_le_of_one_le b1 b2
      calc (p : ℝ) = 1 * p := by ring
        _ ≤ _ := mul_le_mul b4 b3 (by linarith) (by linarith)
    refine le_trans hE (le_trans (le_of_eq ?_) hE0a)
    unfold E0 cPrime
    push_cast
    ring
  have hlog : 1 ≤ Real.logb p a := by
    rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_one]
    exact hpa
  have hkD : ((m + 1 : ℕ) : ℝ) ≤ Dp := by
    refine le_trans ?_ h10
    have c1 : (1 : ℝ) ≤ C * (TT.card : ℝ) := one_le_mul_of_one_le_of_one_le (by linarith) hNR
    have c2 : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := le_self_pow₀ hkR (by norm_num)
    have c3 : ((m + 1 : ℕ) : ℝ) ≤ C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 := by
      calc ((m + 1 : ℕ) : ℝ) = 1 * ((m + 1 : ℕ) : ℝ) := by ring
        _ ≤ _ := mul_le_mul c1 c2 (by linarith) (by linarith)
    exact le_trans c3 (le_mul_of_one_le_right (by positivity) hlog)
  have hkc : m + 1 ≤ cPrime n' r TT.card c0 cpp cStar := by
    have : m + 1 ≤ Dp := by exact_mod_cast hkD
    unfold cPrime
    omega
  have hQ3 : 3 ≤ p ^ goodG' r de h x := by
    calc 3 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ goodG' r de h x := Nat.pow_le_pow_right (by omega) hG1
  have hle := eSP_le (p := p) hF (by omega) hGn hI (m + 1) (cPrime n' r TT.card c0 cpp cStar) t
  have hnum := num_E (cPrime n' r TT.card c0 cpp cStar) r (m + 1) (p ^ goodG' r de h x) (orbitWindowCount r de h x) hkc sq_level_le_degree
    (one_le_orbitWindowCount r de h x) h2 hQ3
  have hfin : eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤
      E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) := by
    unfold E0
    exact le_trans hle hnum
  refine ⟨hfin, ?_⟩
  have hfd := (flatDeg_bounds (by have := hB.m_ge; omega) (by linarith [hB.two_le_a]) h5 t (hTT ▸ ht)).1
  have : ((eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t : ℕ) : ℝ) ≤
      (flatDeg lam0 t : ℝ) := by
    have h0 : ((eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t : ℕ) : ℝ) ≤
        ((E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) : ℕ) : ℝ) := by
      exact_mod_cast hfin
    linarith
  exact_mod_cast this

end Formalism.MainNotions.Pf14
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableIffGeneralRank

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem oHyp_of {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w)
    (φ : WF p n' ≃+* W) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    OHyp p n' O (dvrOfStd h) := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  refine ⟨dvrOfStd_sq h, ?_, ?_⟩
  · show (j.comp (φ : WF p n' →+* W)).Finite
    exact RingHom.Finite.comp h.1.finite (RingHom.Finite.of_surjective _ φ.surjective)
  · show Function.Injective (j.comp (φ : WF p n' →+* W))
    have hj : Function.Injective j := by
      intro a b hab
      have h1 : algebraMap O Kf (j a) = algebraMap O Kf (j b) := congrArg _ hab
      rw [← h.1.ι_comp, ← h.1.ι_comp] at h1
      have := h.1.frac_alt
      exact IsFractionRing.injective W Qq (ι.injective h1)
    exact hj.comp φ.injective

def castVK {n' k r K : ℕ} (hk : k = r + K) : Fin n' × Fin (r + K) → Fin n' × Fin k :=
  fun v => (v.1, Fin.cast hk.symm v.2)

section Lift

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O)

def SymbolRealisableGeneralRank {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hrk : r ≤ k) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) : Prop :=
  ∃ E' : Fin n' → ℕ, (∀ t ∈ F.TT, E' t ≤ E₀ ∧ E' t ≤ deg t) ∧
    ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
    ∀ P ∈ Gen O p K F XXs (G2d F deg E'), ∀ T : ℕ, (∀ mm ∈ P.support, vsDeg mm ≤ T) →
      ∃ Fs : ℕ → ↥((Pol (KK O) (ι := Fin n') k dTop).restrictScalars O),
        (∀ o, HasMultideg (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) dTop ∧
          InWj w (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) 0 ∧
          Realisable p n' w n' r g c' o (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)))) ∧
        ∑ o ∈ Finset.range (T + 1), subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)) =
          MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P) *
            subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q)

theorem symbol_realisable_iff_general_rank {m r K : ℕ} [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) :
    SymbolRealisableAt p n' O w hk hrk F XXs deg dTop c' Q E₀ ↔ SymbolRealisableGeneralRank p n' O w hk hrk F XXs deg dTop c' Q E₀ := Iff.rfl

end Lift

theorem symbol_realisable_general_rank (D : Formalism.BasicNotions.D7) (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) {p n' : ℕ} [Fact p.Prime] [NeZero n']
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p n') O] (S : UniformizedDVR p O)
    (hO : OHyp p n' O S) {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hH : CommonHypotheses p n' r k) (F : Frames n' r)
    (L₁ N₁ G' : ℕ) (hV : F.Valid L₁ N₁) (hT : TwistBound p F (p ^ G')) (hG : ∀ j : ℤ, zF F j - F.fr (j - 1) 0 ≤ G')
    (hK : N₁ + 2 * r ≤ K) (mg : ℤ → ℤ → ℤ) (th o : ℤ → ℤ → ℝ) (hmg : ∀ j x, 0 ≤ mg j x) (deg dTop : Fin n' → ℕ)
    (c' E₀ : ℕ) (hdT : ∀ s, dTop s = if s ∈ F.TT then deg s else 0)
    (hE1 : ∀ t ∈ F.TT, eSP p n' F k c' (p ^ G') t ≤ E₀ ∧ eSP p n' F k c' (p ^ G') t ≤ deg t)
    (hE0 : ∀ t, t ∉ F.TT → eSP p n' F k c' (p ^ G') t = 0) :
    SymbolRealisableGeneralRank p n' O S.w hk hH.2.2.1 F (fun j => XX' O r K F j (mg j) (th j) (o j)) deg dTop c' (p ^ G') E₀ := by
  subst hk
  refine ⟨eSP p n' F (r + K) c' (p ^ G'), hE1, ?_⟩
  intro g hg P hP T hT'
  let X : Ctx p n' r K O :=
    { S := S, hO := hO, hH := hH, Fr := F, L₁ := L₁, N₁ := N₁, G' := G', hV := hV, hT := hT, hG := hG, hK := hK,
      g := g, hg := hg }
  have hd : ∀ s, G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s + eSP p n' F (r + K) c' (p ^ G') s = dTop s := by
    intro s
    unfold G2d
    rw [hdT s]
    by_cases hs : s ∈ F.TT
    · rw [ite_eq_left hs, ite_eq_left hs]
      have := (hE1 s hs).2
      omega
    · rw [ite_eq_right hs, ite_eq_right hs, hE0 s hs]
  have hd0 : ∀ s, s ∉ F.TT → G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s = 0 := by
    intro s hs
    unfold G2d
    rw [ite_eq_right hs]
  have hren : rename (castVK (n' := n') (rfl : r + K = r + K)) P = P := by
    have : (castVK (n' := n') (rfl : r + K = r + K)) = id := by
      funext v
      rfl
    rw [this, rename_id_apply]
  rw [hren]
  exact exists_pol_family_of_mem_gen_of_vsDeg_le X D hW1 hW2 hMon c' mg th o hmg _ _ dTop hd hd0 (SPtrue_hom p n' O F hH.2.2.1 g c' (p ^ G')) P hP T hT'

theorem sources_realisable_holds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz := by
  intro hA _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a15, a16, a17, a18, _, a20, _⟩ := hA
  have hW1 : GeneratorSpanInclusion := generator_pair_conditions_of_admitted D a15 a16
  have hW2 : GeneratorImageIsSymbol := generator_path_homogeneous_holds D a17 a18 a20
  have hMon : RestMon := restMon D
  refine ⟨30, by norm_num, ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ _ K
    _ _ hk hrk F hF
  let _ : Algebra (WF p n') O := algOfIdent j φ
  rw [symbol_realisable_iff_general_rank]
  have hB := hyps_basic (C := C) (by linarith) H
  have hTT := hF.1
  have hGn : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hH : CommonHypotheses p n' r (m + 1) := ⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩
  have eE : E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) =
      E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) := by rw [hk]
  rw [eE]
  show SymbolRealisableGeneralRank p n' O (dvrOfStd hSet).w hk hH.2.2.1 F (fun j => XX' O r K F j _ _ _) _ _ _ _ _
  refine symbol_realisable_general_rank D hW1 hW2 hMon O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x) (goodG' r de h x)
    hF.2.1 (twist_of hF (by have := H.2.1; omega) hGn p (by have := H.1; omega))
    (fun j => (hF.2.2.1 j).le) (by omega) _ _ _ ?_ (flatDeg lam0) (dT TT lam0) (cPrime n' r TT.card c0 cpp cStar) _
    ?_ ?_ ?_
  · intro j x'
    positivity
  · intro s
    unfold dT
    rw [hTT]
  · intro t ht
    exact spdeg hC H hF t ht
  · intro t ht
    exact eSP_off hF _ _ _ t ht

end Formalism.MainNotions.Pf14
end
end
end
