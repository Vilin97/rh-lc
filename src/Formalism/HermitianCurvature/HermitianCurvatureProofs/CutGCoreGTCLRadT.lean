module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTJet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.Analytic.IteratedFDeriv

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTJetRad

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RJR

theorem le_inf (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : ((n : ℕ∞)) ≤ ⊤)

theorem zero_bilin {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {u : D → E} {v : D → F} {s : Set D} {x : D} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s) (n : ℕ) (hvz : ∀ j ≤ n, iteratedFDeriv ℝ j v x = 0) :
    ∀ j ≤ n, iteratedFDeriv ℝ j (fun y => B (u y) (v y)) x = 0 := by
  intro j hj
  have hus : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear hu hv hus hx (n := j) (RJR.le_inf j)
  rw [← norm_le_zero_iff, ← iteratedFDerivWithin_of_isOpen j hs hx]
  refine key.trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero, mul_zero]
  intro i _
  rw [iteratedFDerivWithin_of_isOpen (j - i) hs hx, hvz (j - i) (le_trans (Nat.sub_le _ _) hj),
    norm_zero, mul_zero]

theorem zero_comp {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ψ : ℂ → G} {ζ : D → ℂ} {s : Set D} {t : Set ℂ} {x : D} (hs : IsOpen s) (ht : IsOpen t) (hx : x ∈ s)
    (hmap : Set.MapsTo ζ s t) (hψ : ContDiffOn ℝ ∞ ψ t) (hζ : ContDiffOn ℝ ∞ ζ s) (n : ℕ)
    (hz : ∀ j ≤ n, iteratedFDeriv ℝ j ψ (ζ x) = 0) :
    ∀ j ≤ n, iteratedFDeriv ℝ j (ψ ∘ ζ) x = 0 := by
  intro j hj
  have hus : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hut : UniqueDiffOn ℝ t := ht.uniqueDiffOn
  set Dd : ℝ := ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ + 1 with hDd
  have hD1 : 1 ≤ Dd := by
    have : 0 ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have key := norm_iteratedFDerivWithin_comp_le (n := j) hψ hζ (RJR.le_inf j) hut hus hmap hx
    (C := 0) (D := Dd)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i ht (hmap hx), hz i (le_trans hi hj), norm_zero])
    (fun i hi1 hij => by
      have h1 : ‖iteratedFDerivWithin ℝ i ζ s x‖ ≤ Dd := by
        have : ‖iteratedFDerivWithin ℝ i ζ s x‖ ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ :=
          Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i ζ s x‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hij))
        linarith
      refine h1.trans ?_
      first
        | exact le_self_pow₀ hD1 (by omega)
        | exact le_self_pow hD1 (by omega))
  rw [← norm_le_zero_iff, ← iteratedFDerivWithin_of_isOpen j hs hx]
  simpa using key

def Bc (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] :
    (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℂ).comp
    (ContinuousLinearMap.compL ℂ Wq Wp Wp)).restrictScalars ℝ

def Bd (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] :
    (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℂ).comp
    (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).restrictScalars ℝ

end RJR

open RJR in
theorem jet_radial_holds : GTCLRJetRad := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ Φ q hq N hN
  have hq1 : q.1 ∈ OmX P.r := hq.1
  have hB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, Bs.sec, Bs.π_rep, Bs.π'_rep, Bs.π_cont,
      Bs.π'_cont⟩
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ Φ.2
  have hΦe := (Φ.2).2.2
  let tt : Set ℂ := {ζ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}
  have ht : IsOpen tt := isOpen_lt continuous_const Complex.continuous_normSq
  let ψ : ℂ → (Wq →L[ℂ] Wp) := fun ζ =>
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)
  have hmapQ : Set.MapsTo (fun ζ : ℂ => (q.1, ζ)) tt (NF.QR P.k P.r Bs.z Bs.z') :=
    fun ζ hζ => ⟨hq1, hζ⟩
  have hpair : ContDiff ℝ ∞ (fun ζ : ℂ => (q.1, ζ)) := by
    first
      | exact contDiff_const.prodMk contDiff_id
      | exact contDiff_const.prod contDiff_id
  have hψs : ContDiffOn ℝ ∞ ψ tt := hmem.1.comp hpair.contDiffOn hmapQ
  have hψval : ∀ ζ ∈ tt, ψ ζ = (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec ζ) := by
    intro ζ hζ
    simp only [ψ, NF.radR]
    rw [Set.indicator_of_mem (hmapQ hζ)]
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq
  obtain ⟨V, hV, hg₀V, a, b, ha, hb, hfac⟩ :=
    Formalism.FourierDecayAlt.P.local_smooth_section P.k P.r Bs.z Bs.z' Bs.μsec Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos
      Bs.T'_pos Bs.sec _ hdom.2.1 hdom.2.2
  have hf0 := hfac _ hg₀V hdom.2.1 hdom.2.2
  obtain ⟨Vp, hVp, haVp, Pp, hPp, hPpe⟩ :=
    Formalism.FourierDecayAlt.P.representation_smooth Wp P.k P.r Bs.z Bs.π Bs.z_mem Bs.T_pos Bs.π_rep Bs.π_cont _ hf0.1
  obtain ⟨Vq, hVq, hbVq, Pq, hPq, hPqe⟩ :=
    Formalism.FourierDecayAlt.P.representation_smooth Wq P.k P.r Bs.z' Bs.π' Bs.z'_mem Bs.T'_pos Bs.π'_rep Bs.π'_cont _
      hf0.2.1
  let zL := Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r)
  have hzL : ContDiff ℝ ∞ zL := Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff P.k P.r Bs.z Bs.z' (Fin.last P.r)
  have hz0 : zL (NF.muZ P.k P.r Bs.μsec q.2) = q.2 :=
    Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hq.2
  let W : Set (Q.Mx P.k P.r) := (V ∩ a ⁻¹' Vp) ∩ (V ∩ b ⁻¹' Vq) ∩ zL ⁻¹' tt
  have hW : IsOpen W :=
    ((ha.continuousOn.isOpen_inter_preimage hV hVp).inter
      (hb.continuousOn.isOpen_inter_preimage hV hVq)).inter (ht.preimage hzL.continuous)
  have hg₀W : NF.muZ P.k P.r Bs.μsec q.2 ∈ W := by
    refine ⟨⟨⟨hg₀V, haVp⟩, ⟨hg₀V, hbVq⟩⟩, ?_⟩
    show zL (NF.muZ P.k P.r Bs.μsec q.2) ∈ tt
    rw [hz0]
    exact hq.2
  have hu : ContDiffOn ℝ ∞ (fun g => Pp (a g)) W :=
    hPp.comp (ha.mono fun g hg => hg.1.1.1) fun g hg => hg.1.1.2
  have hu' : ContDiffOn ℝ ∞ (fun g => Pq (b g)) W :=
    hPq.comp (hb.mono fun g hg => hg.1.2.1) fun g hg => hg.1.2.2
  have hv' : ContDiffOn ℝ ∞ (ψ ∘ zL) W := hψs.comp hzL.contDiffOn fun g hg => hg.2
  have hv : ContDiffOn ℝ ∞ (fun g => Bd Wp Wq (Pq (b g)) ((ψ ∘ zL) g)) W :=
    ((Bd Wp Wq).contDiff.comp_contDiffOn hu').clm_apply hv'
  have hF : ContDiffOn ℝ ∞ (fun g => Bc Wp Wq (Pp (a g)) (Bd Wp Wq (Pq (b g)) ((ψ ∘ zL) g))) W :=
    ((Bc Wp Wq).contDiff.comp_contDiffOn hu).clm_apply hv
  have hz1 : ∀ j ≤ N, iteratedFDeriv ℝ j ψ (zL (NF.muZ P.k P.r Bs.μsec q.2)) = 0 := by
    rw [hz0]
    exact hN
  have hv'0 := zero_comp hW ht hg₀W (fun g hg => hg.2) hψs hzL.contDiffOn N hz1
  have hv0 := zero_bilin (Bd Wp Wq) hW hg₀W hu' hv' N hv'0
  have hF0 := zero_bilin (Bc Wp Wq) hW hg₀W hu hv N hv0
  refine ⟨W, _, hW, hg₀W, hF, ?_, hF0⟩
  intro g hg hGl
  have hgt : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq (zL g) := hg.2
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' g := by
    show 0 < Complex.normSq (zL g) - Tz P.k P.r Bs.z * Tz P.k P.r Bs.z'
    exact sub_pos.2 hgt
  obtain ⟨haU, hbU, hfg⟩ := hfac g hg.1.1.1 hGl hGG
  have hdom' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec (q := (q.1, zL g)) ⟨hq1, hgt⟩
  have he := hΦe (q.1, NF.muZ P.k P.r Bs.μsec (zL g)) hdom' (a g) haU (b g) hbU
  have hl : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 g =
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (a g * NF.muZ P.k P.r Bs.μsec (zL g) * b g) := by
    conv_lhs => rw [hfg]
  rw [hl, he]
  simp only
  rw [hPpe (a g) hg.1.1.2 haU, hPqe (b g) hg.1.2.2 hbU, ← hψval (zL g) hgt]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTTaylor

section

@[expose] public section

open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem perm_of_swaps {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W)
    (h : ∀ (a b : Fin n), a ≠ b → ∀ v : Fin n → E, T (v ∘ Equiv.swap a b) = T v) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), T (v ∘ σ) = T v := by
  classical
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro v; rfl
  | swap_mul f x y hxy ih =>
    intro v
    rw [Equiv.Perm.coe_mul]
    calc T (v ∘ (⇑(Equiv.swap x y) ∘ ⇑f)) = T ((v ∘ Equiv.swap x y) ∘ f) := rfl
      _ = T (v ∘ Equiv.swap x y) := ih _
      _ = T v := h x y hxy v

theorem symm_iter : ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (f : E → W) (U : Set E),
    IsOpen U → ContDiffOn ℝ ∞ f U → ∀ x ∈ U, ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  intro n
  induction n with
  | zero =>
    intro W _ _ f U hU hf x hx σ v
    rw [Subsingleton.elim (v ∘ σ) v]
  | succ n ih =>
    intro W _ _ f U hU hf x hx
    refine perm_of_swaps (iteratedFDeriv ℝ (n + 1) f x) ?_
    intro a b hab
    rcases n with _ | m
    · exact absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab
    have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
    have hmul : ∀ σ τ : Equiv.Perm (Fin (m + 1 + 1)),
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ τ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        ∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ ⇑(σ * τ)) = iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro σ τ hσ hτ v
      rw [Equiv.Perm.coe_mul]
      exact (hτ (v ∘ σ)).trans (hσ v)
    have T1 : ∀ a' b' : Fin (m + 1), a' ≠ b' → ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap a'.succ b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro a' b' _ v
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have h0 : (v ∘ Equiv.swap a'.succ b'.succ) 0 = v 0 := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a').symm (Fin.succ_ne_zero b').symm]
      have ht : Fin.tail (v ∘ Equiv.swap a'.succ b'.succ) = Fin.tail v ∘ Equiv.swap a' b' := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [(Fin.succ_injective _).swap_apply]
      rw [h0, ht]
      have hgd : DifferentiableAt ℝ (iteratedFDeriv ℝ (m + 1) f) x :=
        (hfx.iteratedFDeriv_right (m := 1) (i := m + 1) (by
          have := hle (1 + (m + 1)); push_cast at this ⊢; exact this)).differentiableAt one_ne_zero
      rw [← fderiv_continuousMultilinear_apply_const_apply hgd,
        ← fderiv_continuousMultilinear_apply_const_apply hgd]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx)
        (fun y hy => ih W f U hU hf y hy (Equiv.swap a' b') (Fin.tail v)))]
    have T2 : ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 (Fin.succ 0)) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro v
      have hrepr : ∀ w : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x w =
          fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m f)) x (w 0) (Fin.tail w 0) (Fin.tail (Fin.tail w)) := by
        intro w
        rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
        first
        | rfl
        | simp [continuousMultilinearCurryLeftEquiv_symm_apply]
      rw [hrepr, hrepr]
      have hg : ContDiffAt ℝ 2 (iteratedFDeriv ℝ m f) x :=
        hfx.iteratedFDeriv_right (by have := hle (2 + m); push_cast at this ⊢; exact this)
      have hs := hg.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
      have e0 : (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = Fin.tail v 0 := by
        simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.tail]
      have e1 : Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = v 0 := by
        simp only [Fin.tail, Function.comp_apply, Equiv.swap_apply_right]
      have e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0))) = Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))]
      rw [e0, e1, e2, hs (Fin.tail v 0) (v 0)]
    have T0 : ∀ b' : Fin (m + 1), ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro b'
      by_cases hb : b' = 0
      · subst hb; exact T2
      · have e := Equiv.swap_mul_swap_mul_swap (x := (0 : Fin (m + 1 + 1))) (y := Fin.succ 0)
          (z := b'.succ) (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero b').symm
        rw [Equiv.swap_comm, ← e]
        have h1 := T1 0 b' (Ne.symm hb)
        exact hmul _ _ (hmul _ _ h1 T2) h1
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd rfl hab
      | succ b' => exact T0 b'
    | succ a' =>
      cases b using Fin.cases with
      | zero => intro v; rw [Equiv.swap_comm]; exact T0 a' v
      | succ b' => exact T1 a' b' (fun h => hab (h ▸ rfl))

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem poly_contDiff {j : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) (a : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ζ => m (fun _ => ζ - a)) := m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)

theorem poly_hom {j i : ℕ} (hij : i ≠ j) (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ)) 0 = 0 := by
  have hg : ContDiff ℝ i (fun ζ : E => m (fun _ => ζ)) :=
    m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  set L : E →L[ℝ] E := (2 : ℝ) • ContinuousLinearMap.id ℝ E with hL
  have hcomp : (fun ζ : E => m (fun _ => ζ)) ∘ L = ((2 : ℝ) ^ j) • (fun ζ : E => m (fun _ => ζ)) := by
    funext ζ
    simp only [Function.comp_apply, Pi.smul_apply, hL, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [m.map_smul_univ (fun _ => (2 : ℝ)) (fun _ => ζ)]
    simp [Finset.prod_const]
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_right L hg 0 (i := i) le_rfl
  rw [hcomp, iteratedFDeriv_const_smul_apply hg.contDiffAt, map_zero] at h1
  have hne : (2 : ℝ) ^ j ≠ (2 : ℝ) ^ i := by
    intro h
    apply hij
    have : (2 : ℕ) ^ j = 2 ^ i := by exact_mod_cast h
    exact (Nat.pow_right_injective le_rfl this).symm
  ext v
  have key : ((2 : ℝ) ^ j) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v =
      ((2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v := by
    have hv := congrArg (fun T => T v) h1
    simp only [ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply] at hv
    rw [hv, hL]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0)
      (fun _ => (2 : ℝ)) v]
    simp [Finset.prod_const]
  have h0 : ((2 : ℝ) ^ j - (2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v = 0 := by
    rw [sub_smul, key, sub_self]
  rw [ContinuousMultilinearMap.zero_apply]
  exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

theorem poly_at {j i : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) (a : E) (v : Fin i → E) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ - a)) a v =
      if h : i = j then ∑ σ : Equiv.Perm (Fin j), m (fun k => (v ∘ Fin.cast h.symm) (σ k)) else 0 := by
  by_cases h : i = j
  · subst h
    rw [dite_eq_left rfl, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self,
      ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
    rfl
  · rw [dite_eq_right h, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self, poly_hom h m]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

theorem taylor_expansion_holds : GTCLRTaylor := by
  intro V _ _ ψ U ζ₀ N hU hζ hψ i hi
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  have hψat : ContDiffAt ℝ i ψ ζ₀ := (hψ.contDiffAt (hU.mem_nhds hζ)).of_le (hle i)
  have hS : ContDiff ℝ i (fun ζ : ℂ => ∑ j ∈ Finset.range (N + 1),
      ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) :=
    ContDiff.sum fun j _ => (poly_contDiff _ _).const_smul _
  refine (iteratedFDeriv_sub_apply hψat hS.contDiffAt).trans ?_
  rw [sub_eq_zero, iteratedFDeriv_sum (fun j _ => (poly_contDiff _ _).const_smul _)]
  ext v
  rw [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      iteratedFDeriv ℝ i (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ v =
        if j = i then ((i.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ)
        else 0 := by
    intro j _
    rw [show (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) =
        ((j.factorial : ℝ)⁻¹) • (fun ζ : ℂ => iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) from rfl,
      iteratedFDeriv_const_smul_apply ((poly_contDiff _ _).contDiffAt),
      ContinuousMultilinearMap.smul_apply, poly_at]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (N + 1)) i,
    if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hi))]
  have hs : ∀ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ) = iteratedFDeriv ℝ i ψ ζ₀ v :=
    fun σ => symm_iter i V ψ U hU hψ ζ₀ hζ σ v
  rw [Finset.sum_congr rfl (fun σ _ => hs σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)), one_smul]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadT

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem radial_torus_local_holds : GTCLRadT :=
  radial_torus_of_jets_taylor jet_finite_order_along_level jet_radial_holds taylor_expansion_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end
