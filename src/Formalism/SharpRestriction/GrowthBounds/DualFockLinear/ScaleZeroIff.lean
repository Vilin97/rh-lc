module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable
import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.ProdBlockEmbMonomial
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRLinDual
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EvensBeforePairwise
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleNegMono
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.LaTwInvT
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.PairFormula
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockR
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRAddRight

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockSumRight

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (kapR kapR_alg)

theorem fock_sum_right {R : Type} [CommRing R] {τ : Type} {ι : Type} (s : Finset ι) (F : MvPolynomial τ R)
    (G : ι → MvPolynomial τ R) : fock F (∑ q ∈ s, G q) = ∑ q ∈ s, fock F (G q) := by
  simp only [fock, MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem inWj_map {O : Type} [CommRing O] [IsDomain O] {τ : Type} (w : O) (P : MvPolynomial τ O) :
    InWj w (MvPolynomial.map (algebraMap O (KK O)) P) 0 := by
  intro m
  exact ⟨P.coeff m, by simp [MvPolynomial.coeff_map]⟩

theorem valLe_perturb {O Kf : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field Kf] [Algebra O Kf] (p : ℕ) (w : O)
    (hw : ¬ IsUnit w) (hsq : w ^ 2 = (p : O)) (D c : ℕ) (hc : 2 * D < c) (a b z : O) (hab : a * b = (p : O) ^ D) :
    ValLe (Kf := Kf) (p : O) D (algebraMap O Kf (a + w ^ c * z)) := by
  obtain ⟨k, hk⟩ : ∃ k, c = 2 * D + (k + 1) := ⟨c - 2 * D - 1, by omega⟩
  have hwc : w ^ c = (p : O) ^ D * w ^ (k + 1) := by rw [hk, pow_add, pow_mul, hsq]
  have hwk : w ^ (k + 1) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => hw ((isUnit_pow_iff (Nat.succ_ne_zero k)).1 h)
  have hm : b * w ^ (k + 1) * z ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hwk)

  have hu : IsUnit (1 + b * w ^ (k + 1) * z) := by
    by_contra hne
    have h1 : (1 + b * w ^ (k + 1) * z) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).2 hne
    have h2 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ h1 hm
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have ha' : a + w ^ c * z = a * (1 + b * w ^ (k + 1) * z) := by rw [hwc, ← hab]; ring
  refine ⟨a + w ^ c * z, b * ↑hu.unit⁻¹, rfl, ?_⟩
  rw [ha', mul_mul_mul_comm, IsUnit.mul_val_inv, mul_one, hab]



theorem restFlat_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hXi : RestXi D CLa Ck Crk Cdeg CH CE C6 C18) (hRe : RestReal D CLa Ck Crk Cdeg) :
    RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA _ h14b
  obtain ⟨Ct0, CDf, C₂, h0, h1, hC2, hX⟩ := hXi hA h14b
  obtain ⟨C₃, hC3, hR⟩ := hRe hA
  obtain ⟨C6U, hC6U, h6⟩ := one_sided_lemma4_of_admitted_theorem_II
  have h6' := h6 D CLa Ck Crk Cdeg hA
  obtain ⟨C₄, hC4, hII⟩ := hypII_at C6U (C6U + 1) C6U
  refine ⟨Ct0, CDf, max (max C₂ C₃) (max C₄ CDf), h0, h1,
    lt_of_lt_of_le hC2 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have c2 : C₂ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCC
  have c3 : C₃ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCC
  have c4 : C₄ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCC
  have c5 : CDf ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCC
  obtain ⟨tF, DX, htF, hDX, hxi⟩ := hX C c2 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨gv, hgv, hreal⟩ := hR C c3 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨hII1, hcP⟩ := hII C c4 p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H F hFr
  have hBas := hyps_basic (C := C) (le_trans hC4 c4) H
  have hGn : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  have hH : CommonHypotheses p n' r (m + 1) := ⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩
  have hw0 : algebraMap O Kf w ≠ 0 := Formalism.L2.G.Model.w_ne hSet.1

  have hlog : 0 ≤ (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
    have h2a := hBas.two_le_a
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have := H.1
      have : 1 < p := by omega
      exact_mod_cast this
    have : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
    positivity
  have hDp : (DX : ℝ) ≤ Dp := by
    have h10 : C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp := H.2.2.2.2.2.2.2.2.2.1
    have : CDf * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤
        C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
      have e1 : ∀ t : ℝ, t * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a =
          t * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) := fun t => by ring
      rw [e1, e1]
      exact mul_le_mul_of_nonneg_right c5 hlog
    linarith
  have hDp' : DX ≤ Dp := by exact_mod_cast hDp
  have h2D : 2 * DX < cPrime n' r TT.card c0 cpp cStar := by
    have h11 : 8 * (Dp + 1) ≤ cStar := H.2.2.2.2.2.2.2.2.2.2.1
    unfold cPrime
    omega
  refine ⟨tF, DX, htF, hDX, ?_⟩
  intro F1 f1 f2 f3
  obtain ⟨nq, o, sig, hsig, hval⟩ := hxi F1 f1 f2 f3
  have hT : ∀ q, ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))),
      T ∈ scale (algebraMap O Kf w ^ (-(tF : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
      T ∈ Re' p ι σ w r (flW (dT TT lam0)) e ∧
      (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
        T ∈ scale (algebraMap O Kf w ^ ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℤ))
          (Re' p ι σ w r (flW (dT TT lam0)) e')) ∧
      ∃ z : O, be p r (flW (dT TT lam0)) (Θ F1) T =
        kapR hSet.1 ((p : KK O) ^ (kapFl p (m + 1) (dT TT lam0)) *
          fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (sig q) /
            (((∏ s, (dT TT lam0 s).factorial : ℕ) : ℕ) : KK O)) +
          algebraMap O Kf (w ^ (cPrime n' r TT.card c0 cpp cStar) * z) := by
    intro q
    obtain ⟨ho, hmd, hL4⟩ := hsig q
    have hint : InWj w (sig q) 0 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hs⟩ := hL4
      rw [hs]
      exact inWj_map w _
    have hrl : Realisable p n' w n' r gv (cPrime n' r TT.card c0 cpp cStar) (o q) (sig q) := by
      rw [← hcP] at hL4 ⊢
      exact one_sided_lemma4_realisable D C6U (C6U + 1) C6U h6' O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x)
        (goodG' r de h x) hFr.2.1 (twist_of hFr (by have := H.2.1; omega) hGn p (by have := H.1; omega))
        (flatDeg lam0) ⌈a⌉₊ Y c0 0 (cStar + 2 * r * n' * cpp) (Dp : ℝ) hII1 gv hgv (o q) (sig q) hL4
    obtain ⟨T, t1, t2, t3, t4⟩ := hreal (o q) (sig q) hmd hint hrl
    exact ⟨T, scale_neg_mono w hw0 ho _ t1, t2, t3, t4 F1 f2⟩
  choose T t1 t2 t3 z t4 using hT
  refine ⟨∑ q, T q, Submodule.sum_mem _ fun q _ => t1 q, Submodule.sum_mem _ fun q _ => t2 q,
    fun e' he' htg hne => Submodule.sum_mem _ fun q _ => t3 q e' he' htg hne, ?_⟩
  obtain ⟨aa, bb, hx1, hab⟩ := hval
  have hbe : be p r (flW (dT TT lam0)) (Θ F1) (∑ q, T q) =
      algebraMap O Kf (aa + w ^ (cPrime n' r TT.card c0 cpp cStar) * ∑ q, z q) := by
    have e1 : be p r (flW (dT TT lam0)) (Θ F1) (∑ q, T q) = ∑ q, be p r (flW (dT TT lam0)) (Θ F1) (T q) := by
      unfold be
      rw [LinearMap.sum_apply]
    rw [e1]
    simp only [t4, Finset.sum_add_distrib]

    rw [← map_sum, ← Finset.sum_div, ← Finset.mul_sum, ← fock_sum_right, hx1, kapR_alg, map_add (f := _), ← map_sum,
    ← Finset.mul_sum]
  rw [hbe]
  exact valLe_perturb p w hSet.2.1.not_isUnit hSet.1.w_sq DX _ h2D aa bb _ hab

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ScaleZeroIff

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_Pol dE invT_mul_D dual_edgeBasis dual_edge edgeBasis latDual_colSpan w_ne p_eq pQ_ne
  kapR kapR_alg pol_iff inWj_iff pol_of_map)
open Formalism.L2.G.Model.TS

theorem scale_zero_iff {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
    [IsScalarTower O Kf X] (c : Kf) (M : Submodule O X) (x : X) : x ∈ scale (c ^ (0 : ℤ)) M ↔ x ∈ M := by
  rw [mem_scale]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x, h, by simp⟩

section

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}



theorem realAt_gen (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (hm1 : 1 ≤ m) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m + 1) (d : Fin n' → ℕ) (cP κ : ℕ)
    (hMD : MultDiv O p κ (k := m + 1) d)
    (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e)
    (htgt : e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq))
    (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
    (hhm : IsUnit hm.det) (hg : IsGLW g) (hbasis : IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hΘ : IsTrueTheta hS d (flW d) (vecE n') hm Θ) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∃ gv : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW gv ∧
    ∀ (o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O)), HasMultideg sig d → InWj w sig 0 →
      Realisable p n' w n' r gv cP o sig →
      ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) d)),
        T ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW d) e.tgt)) ∧
        T ∈ Re' p ι σ w r (flW d) e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          T ∈ scale (algebraMap O Kf w ^ (cP : ℤ)) (Re' p ι σ w r (flW d) e')) ∧
        ∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
          Θ F ∈ Re p ι σ w r (flW d) e →
          ∃ z : O, be p r (flW d) (Θ F) T =
            kapR hS ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O))) sig /
              (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) + algebraMap O Kf (w ^ cP * z) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have h1d : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq).det := by simp
  have h1T : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)⁻¹).transpose = 1 := by simp
  set b := hm * ((matQ φ g)⁻¹).transpose with hbdef
  have htg : e.tgt = colSpan W (b * lb_D (m + 1) r ((p : ℕ) : Qq)) := hbasis.2.2
  obtain ⟨gv, hgv, hgvX⟩ := exists_gv hS φ (b * lb_D (m + 1) r ((p : ℕ) : Qq)) (by rw [← htg, htgt])
  have hrel : ((matQ φ gv)⁻¹).transpose = (b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq) := by
    rw [hgvX]
    exact invT_mul_D b hbasis.1 r _ (pQ_ne hS)
  have hbv : IsEdgeBasis p r e.dual (1 * ((matQ φ gv)⁻¹).transpose) := by
    rw [Matrix.one_mul, hrel]
    exact dual_edgeBasis p r (pQ_ne hS) e b hbasis
  obtain ⟨Θv, ⟨hv1, hv2⟩, hv3⟩ := theta_exists p n' W Qq O Kf ι σ j w hS φ hφ m r (vecE n') d (flW d) hr1 hr2
    (isFlat_flW d) 1 h1d
  obtain ⟨Θ', ⟨_, h2'⟩, h3'⟩ := theta_exists p n' W Qq O Kf ι σ j w hS φ hφ m r (vecE n') d (flW d) hr1 hr2
    (isFlat_flW d) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun F => Subtype.ext ((hΘ F).trans (h3' F).symm)
  subst hΘeq
  obtain ⟨thK, hthK⟩ := exists_thK Kf hm1 d
  obtain ⟨hE1, _, hE3⟩ := edgePlane p n' W Qq O Kf ι σ j w hS φ hφ m r 1 h1d
  refine ⟨gv, hgv, ?_⟩
  intro o sig hmd hint hreal
  obtain ⟨Ff, hA, hmdF, hsym, hoth⟩ := hreal
  let F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) := ⟨Ff, hmdF d hmd⟩
  set cc : Kf := (p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf) with hcc
  refine ⟨TY thK cc ((algebraMap O Kf w ^ (-(o : ℤ))) • Θv F'), ?_, ?_, ?_, ?_⟩
  · rw [htgt]
    apply FD_HL thK hS hm1 hthK κ hMD 1 h1d
    rw [h1T]
    exact mem_scale.2 ⟨Θv F', (hv1 F').1 hA, rfl⟩
  · rw [← scale_zero_iff (algebraMap O Kf w)]
    apply FD_edge thK hS hm1 hthK κ hMD r e b hbasis
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) gv
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + 0) := by
      intro mm
      obtain ⟨c1, hc1⟩ := hsym mm
      obtain ⟨c2, hc2⟩ := hint mm
      refine ⟨c2 + w ^ cP * c1, ?_⟩
      have e1 : AddMonoidAlgebra.coeff (subst p n' O w n' r gv Ff) mm =
          AddMonoidAlgebra.coeff (subst p n' O w n' r gv Ff - C (algebraMap O (KK O) (w ^ o)) * sig) mm +
            algebraMap O (KK O) (w ^ o) * AddMonoidAlgebra.coeff sig mm := by
        rw [MvPolynomial.coeff_sub, coeff_C_mul]
        ring
      show AddMonoidAlgebra.coeff (subst p n' O w n' r gv Ff) mm = _
      rw [e1, hc1, hc2, ← map_mul, ← map_add (f := _)]
      congr 1
      ring
    have h2 := (hv2 gv hgv e.dual hbv F' (o + 0)).1 h1
    exact scale_shift (algebraMap O Kf w) hw o 0 _ h2
  · intro e' he' htg' hne
    obtain ⟨b', hb'⟩ := edgeBasis hS m r e' he'
    apply FD_edge thK hS hm1 hthK κ hMD r e' b' hb'
    have hd' := dual_edge hS m r e' he'
    have hd := dual_edge hS m r e he
    have hsrc : e'.dual.src = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) := by
      show latDual e'.tgt = _
      rw [htg', htgt, latDual_colSpan _ h1d, h1T]
    obtain ⟨g', hg', hbg'⟩ := hE1 e'.dual hd'.1 hsrc
    have hpl : ratPlane p n' r g' ≠ ratPlane p n' r gv := by
      intro hEq
      have h5 : e'.dual = e.dual := (hE3 g' gv e'.dual e.dual hg' hgv hbg' hbv).2 hEq
      apply hne
      rw [← hd'.2, h5, hd.2]
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) g'
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + cP) := hoth g' hg' hpl
    have h2 := (hv2 g' hg' e'.dual hbg' F' (o + cP)).1 h1
    exact scale_shift (algebraMap O Kf w) hw o cP _ h2
  · intro F hF
    have hpf := pair_formula thK hS φ hφ r hr1 hr2 hthK κ hm hhm g gv hg hgv hbasis.1 hrel Θ Θv hΘ hv3 F F'

    have hF0 : InWjRg p n' O w r (flatLetters (vecE n')) g (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) 0 :=
      (h2' g hg e hbasis F 0).2 (by
        have : ((0 : ℕ) : ℤ) = 0 := rfl
        rw [this, scale_zero_iff]
        exact hF)
    obtain ⟨G0, hG0⟩ := (inWj_iff hS _ 0).1 hF0
    rw [pow_zero, one_smul] at hG0
    have hG0' : map (kapR hS) (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O))) =
        map (algebraMap O Kf) G0 := hG0
    have hG0P : G0 ∈ Pol O (m + 1) d := by
      apply pol_of_map hS
      rw [← hG0', subst_Lin hS φ hφ r hm hhm g hg F.1 F.2]
      exact Submodule.smul_mem _ _ (Lin_Pol _ _ (Lin_Pol _ _ ((pol_iff hS _ _ _).1 F.2)))
    obtain ⟨E, hE⟩ := (inWj_iff hS _ (o + cP)).1 hsym
    obtain ⟨z, hz⟩ := int_pair (Kf := Kf) p κ hMD G0 hG0P E
    refine ⟨z, ?_⟩
    set SF := subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O)) with hSF
    set Rr := subst p n' O w n' r gv Ff - C (algebraMap O (KK O) (w ^ o)) * sig with hRr
    have e1 : subst p n' O w n' r gv (F' : MvPolynomial (TV n' (m + 1)) (KK O)) =
        algebraMap O (KK O) (w ^ o) • sig + Rr := by
      rw [hRr, smul_eq_C_mul]
      show subst p n' O w n' r gv Ff = _
      ring
    have e2 : be p r (flW d) (Θ F) (TY thK cc ((algebraMap O Kf w ^ (-(o : ℤ))) • Θv F')) =
        algebraMap O Kf w ^ (-(o : ℤ)) * be p r (flW d) (Θ F) (TY thK cc (Θv F')) := by
      simp only [be, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have e3 : kapR hS (fock SF Rr) = algebraMap O Kf w ^ (o + cP) *
        fockR (map (algebraMap O Kf) G0) (map (algebraMap O Kf) E) := by
      rw [fock_eq_fockR, ← fockR_map, hG0', hE, tsact_smul_right]
    rw [e2, hpf, e1, fock_eq_fockR, fockR_add_right, tsact_smul_right, ← fock_eq_fockR, ← fock_eq_fockR]
    have e4 : kapR hS ((p : KK O) ^ κ * (algebraMap O (KK O) (w ^ o) * fock SF sig + fock SF Rr) /
        (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) =
        algebraMap O Kf w ^ o * kapR hS ((p : KK O) ^ κ * fock SF sig / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) +
          algebraMap O Kf w ^ (o + cP) * algebraMap O Kf z := by
      rw [← hz]
      simp only [map_div₀, map_mul, map_add (f := _), map_pow, map_natCast, kapR_alg, e3]
      ring
    rw [e4, zpow_neg, zpow_natCast, map_mul, map_pow, pow_add]
    field_simp

end

theorem realStep (C CLa : ℝ) : RealStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  exact realAt_gen hSet.1 φ hφ (by omega) r (by omega) (by omega) (dT TT lam0) _ _
    (multDiv_kapFl O p (dvrOfStd hSet).p_mem (dT TT lam0)) e he htgt hm g hhm hg hbasis Θ hΘ

theorem restReal (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestReal D CLa Ck Crk Cdeg :=
  fun _ => ⟨1, one_pos, fun C _ => realStep C CLa⟩

theorem restFlat_of_Xi (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hXi : RestXi D CLa Ck Crk Cdeg CH CE C6 C18) : RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 :=
  restFlat_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hXi (restReal D CLa Ck Crk Cdeg)

end Formalism.MainNotions.TestSideCounting
end
end
end
