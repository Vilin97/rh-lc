module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.VFlatSupported
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBAtOfRho
public import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
public import Formalism.LocalToGlobal.GroupLattices.FockModels.MulMemRiemannRochSpaceAdd
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeMulOfWeightSum
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RankMulConductorDivLeOne
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
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBStepOfRho

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def RhoStep (C CK : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        RhoAt p n' ι σ w r TT lam0 c0 (r * TT.card * c0 + 2 * r * n' * cpp)
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e Θ

def RestRho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → RhoStep C CK

theorem cloudBStep_of_rho (D : Formalism.BasicNotions.D7) (C CK CLa : ℝ) (hR : RhoStep C CK) : CloudBStep C CK CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hw : algebraMap O Kf w ≠ 0 := w_ne_zero hSet.1
  obtain ⟨Θ', hΘ1, hΘ2⟩ := theta_exists p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (vecE n') (dT TT lam0) (flW (dT TT lam0))
    (by omega) (by omega) (isFlat_flW _) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun G => Subtype.ext (by rw [hΘ G, hΘ2 G])
  have hFs : ∀ b, Θ (FsB b) ∈ Re p ι σ w r (flW (dT TT lam0)) e := by
    intro b
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) g (FsB b : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) 0 := by
      show InWj w (subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O))) 0
      rw [hFsB b]
      unfold symB toK
      rw [subst_SPtrue w F hF.2.1 hSet.1.even (by omega) hrk hg, ← map_mul]
      intro mm
      exact ⟨AddMonoidAlgebra.coeff _ mm, by rw [coeff_map, pow_zero, one_mul]⟩
    have h2 := (hΘ1.2 g hg e hbasis (FsB b) 0).1 h1
    rw [hΘeq]
    obtain ⟨z, hz, hze⟩ := mem_scale.1 h2
    rw [← hze]
    simpa using hz
  refine cloudBAt_of_rho hSet.1 Formalism.L2.G.Model.bePerfect r TT lam0 hdom c0 _ _ e he FsB Θ ?_
    (hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ e he htgt hm g hhm hg hbasis
      Θ hΘ)
  intro b s u hs hu
  exact edge_lattice_mul_of_weight_sum D (Formalism.L2.G.Model.products_sections_integral D) p ι σ w hw r (lambda_zero_eq_product TT lam0) (flW_dom _)
    (restW_dom (by omega) TT lam0 hdom) e hu (hFs b) hs

theorem restCloudB_of_rho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRho D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => cloudBStep_of_rho D C CK CLa (h3 C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfTop

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def topW {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then X s else 0

def specW {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then 0 else X s

theorem topW_dom {n' m : ℕ} (TT : Finset (Fin n')) {X : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant X) :
    IsDominant (topW TT X) := by
  intro s
  unfold topW
  split_ifs
  · exact h s
  · exact anti_zero m

theorem specW_dom {n' m : ℕ} (TT : Finset (Fin n')) {X : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant X) :
    IsDominant (specW TT X) := by
  intro s
  unfold specW
  split_ifs
  · exact anti_zero m
  · exact h s

theorem top_add_spec {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) : X = topW TT X + specW TT X := by
  funext s
  by_cases h : s ∈ TT <;> simp [topW, specW, h]

theorem peel_self {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) :
    Peel TT X (topW TT X) (specW TT X) :=
  ⟨fun s hs => by simp [topW, specW, hs], fun s hs => by simp [topW, specW, hs]⟩

theorem restW_off {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (hs : s ∉ TT) :
    restW TT lam0 s = lam0 s := by
  funext i
  simp [restW, flW, dT, hs]

theorem specW_rest {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    specW TT (restW TT lam0) = specW TT lam0 := by
  funext s
  by_cases h : s ∈ TT
  · simp [specW, h]
  · simp only [specW, if_neg h, restW_off TT lam0 s h]

theorem card_lt_le (m r : ℕ) : (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card ≤ r := by
  calc (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card ≤ (Finset.range r).card := by
        refine Finset.card_le_card_of_injOn (fun a => a.val) ?_ (Fin.val_injective.injOn)
        intro a ha
        simpa using ha
    _ = r := Finset.card_range r

theorem ordMax_spec {n' m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (cpp : ℕ)
    (hb : ∀ s, s ∉ TT → ∀ i, |lam0 s i| ≤ cpp) : ordMax r (specW TT lam0) ≤ ((2 * r * n' * cpp : ℕ) : ℤ) := by
  unfold ordMax
  have h1 : ∀ s : Fin n', ∀ a : Fin (m + 1),
      lamAt (specW TT lam0) s a - lamAt (specW TT lam0) s (Fin.last m) ≤ 2 * (cpp : ℤ) := by
    intro s a
    by_cases hs : s ∈ TT
    · rw [lamAt_zero (by simp [specW, hs])]
      simp
    · have hz : specW TT lam0 s = lam0 s := by simp [specW, hs]
      have hb' := hb s hs
      unfold lamAt
      rw [hz]
      split_ifs
      · have := abs_le.1 (hb' a)
        have := abs_le.1 (hb' (Fin.last m))
        omega
      · have := abs_le.1 (hb' a.rev)
        have := abs_le.1 (hb' (Fin.last m).rev)
        show -lam0 s a.rev - -lam0 s (Fin.last m).rev ≤ 2 * (cpp : ℤ)
        omega
  calc ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r,
        (lamAt (specW TT lam0) s a - lamAt (specW TT lam0) s (Fin.last m))
      ≤ ∑ _s : Fin n', ∑ a : Fin (m + 1) with a.val < r, 2 * (cpp : ℤ) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => h1 s a
    _ = ∑ _s : Fin n', ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) * (2 * (cpp : ℤ)) := by
        simp [Finset.sum_const]
    _ ≤ ∑ _s : Fin n', (r : ℤ) * (2 * (cpp : ℤ)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        have := card_lt_le m r
        have h2 : ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) ≤ r := by exact_mod_cast this
        nlinarith [Int.natCast_nonneg cpp]
    _ = ((2 * r * n' * cpp : ℕ) : ℤ) := by
        simp [Finset.sum_const]
        ring

def RhoTopStep (C CK : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        ∃ κ : ℕ, (κ : ℝ) ≤ CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ∧
          RhoAtG p n' ι σ w r TT (dT TT lam0) (topW TT (restW TT lam0)) (topW TT lam0) c0 (r * TT.card * c0) κ e Θ

def RestRhoTop (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → RhoTopStep C CK

theorem rhoStep_of_top (D : Formalism.BasicNotions.D7) (C CK : ℝ) (hR : RhoTopStep C CK) : RhoStep C CK := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  obtain ⟨κ, hκ, hT⟩ := hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hb : ∀ s, s ∉ TT → ∀ i, |lam0 s i| ≤ cpp := fun s hs => (H.2.2.2.2.1.1 s).2 hs
  refine rhoAt_of_G p n' ι σ w r TT lam0 c0 _ _ e Θ κ hκ ?_
  have hPr : Peel TT (restW TT lam0) (topW TT (restW TT lam0)) (specW TT lam0) := by
    have := peel_self TT (restW TT lam0)
    rwa [specW_rest] at this
  have hrest : restW TT lam0 = topW TT (restW TT lam0) + specW TT lam0 := by
    have := top_add_spec TT (restW TT lam0)
    rwa [specW_rest] at this
  exact rho_peel D hSet.1 r TT (dT TT lam0) (fun s hs => by simp [dT, hs]) (restW TT lam0) lam0
    (topW TT (restW TT lam0)) (topW TT lam0) (specW TT lam0) (peel_self TT lam0) hPr (topW_dom TT hdom)
    (specW_dom TT hdom) (top_add_spec TT lam0) hrest c0 (r * TT.card * c0) κ (2 * r * n' * cpp)
    (ordMax_spec r TT lam0 cpp hb) e he Θ hT

theorem restRho_of_top (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRhoTop D CLa Ck Crk Cdeg) :
    RestRho D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => rhoStep_of_top D C CK (h3 C hC)⟩

theorem restCloudB_of_top (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRhoTop D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_rho D CLa Ck Crk Cdeg (restRho_of_top D CLa Ck Crk Cdeg h)

end Formalism.MainNotions.TestSideCounting
end
end
end
