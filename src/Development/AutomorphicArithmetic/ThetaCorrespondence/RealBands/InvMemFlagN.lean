module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Imports

section

@[expose] public section

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.exists_split :
    ∀ (n : ℕ) (ε : Fin n → Bool) (j : Fin 1 → ℕ) (W : Flag n 1), IsIsoFlag ε j W →
      ∃ a : ℝ → UJ ε, Continuous a ∧ (∀ s t, a (s + t) = a s * a t) ∧ ∀ t, IsSplit ε W (fun _ => t) (a t) := by
  intro n ε j W hW
  obtain ⟨P, h0, h1, h2⟩ := GlobalTheory.RealIwasawa.exists_proj (W (Fin.last 1))
  have hJ := Jm_mul_self ε
  have hPP : P * P = P := Matrix.ext_iff_mulVec.2 fun y => by rw [← mulVec_mulVec, h2 _ (h1 y)]
  have hi : P * Jm ε * P = 0 := GlobalTheory.RealIwasawa.proj_iso hW h0 fun y => h1 y
  have key : ∀ r : ℝ, ∃ t : UJ ε,
      uMat t = GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)) := by
    intro r
    set Q := Jm ε * P * Jm ε with hQ
    have hQQ : Q * Q = Q := by
      simp only [hQ, mul_assoc]; rw [← mul_assoc (Jm ε) (Jm ε), hJ, one_mul, ← mul_assoc P P, hPP]
    have hPQ : P * Q = 0 := by rw [hQ, ← mul_assoc, ← mul_assoc, hi, zero_mul]
    have hQP : Q * P = 0 := by rw [hQ, mul_assoc, mul_assoc, ← mul_assoc P, hi, mul_zero]
    set c : ℂ := (Real.exp r : ℂ) with hc
    set d : ℂ := (Real.exp (-r) : ℂ) with hd
    have hH : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ = GlobalTheory.IsoTorus.tor P Q c d := by
      simp [GlobalTheory.IsoTorus.tor, hQ, h0, Jm_conjTranspose, hc, hd, mul_assoc, -Complex.ofReal_exp]
    have hm : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ * Jm ε * GlobalTheory.IsoTorus.tor P Q c d = Jm ε := by
      have e : GlobalTheory.IsoTorus.tor P Q c d * Jm ε = Jm ε * GlobalTheory.IsoTorus.tor P Q d c := by
        simp only [GlobalTheory.IsoTorus.tor, hQ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
          mul_assoc, hJ, ← mul_assoc (Jm ε) (Jm ε)]
        abel
      rw [hH, e, mul_assoc, GlobalTheory.IsoTorus.tor_tor hPP hQQ hPQ hQP, hc, hd, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      simp [GlobalTheory.IsoTorus.tor_one]
    obtain ⟨t, ht, -⟩ := GlobalTheory.RealIwasawa.exists_uMat _ hm
    exact ⟨t, ht⟩
  choose a ha using key
  have hs : ∀ t, IsSplit ε W (fun _ => t) (a t) := fun t => by
    convert isSplit_of_tor hW h0 h1 h2 (ha t) using 2 with i
    rw [if_pos (Fin.le_last _)]
  refine ⟨a, ?_, fun s t => ?_, hs⟩
  · refine (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff.2 ?_
    refine Continuous.congr (f := fun r : ℝ => GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)))
      ?_ fun r => (ha r).symm
    unfold GlobalTheory.IsoTorus.tor
    fun_prop
  · exact (existsUnique_isSplit hW (fun _ => s + t)).unique (hs _) ((hs s).mul (hs t))
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.InvMemFlagN

section

@[expose] public section

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem act_mul {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) (y : Fin n → ℂ) :
    uMat (g * h) *ᵥ y = uMat g *ᵥ (uMat h *ᵥ y) := by
  rw [mulVec_mulVec]; rfl

private theorem act_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (y : Fin n → ℂ) :
    uMat g⁻¹ *ᵥ (uMat g *ᵥ y) = y := by
  rw [← act_mul, inv_mul_cancel]; exact one_mulVec y

private theorem act_inv' {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (y : Fin n → ℂ) :
    uMat g *ᵥ (uMat g⁻¹ *ᵥ y) = y := by
  rw [← act_mul, mul_inv_cancel]; exact one_mulVec y

private theorem keeps_perp {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p : UJ ε} (hp : p ∈ parab ε W)
    {y : Fin n → ℂ} (hy : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) :
    ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat p *ᵥ y)) = 0 := by
  intro z hz
  have hpiS : ∀ i, ∀ y ∈ W i, uMat p⁻¹ *ᵥ y ∈ W i := (parab ε W).inv_mem hp
  have h1 : Jm ε *ᵥ (uMat p *ᵥ y) = (uMat p⁻¹)ᴴ *ᵥ (Jm ε *ᵥ y) := by
    rw [mulVec_mulVec, mulVec_mulVec, conjTranspose_inv_mul_Jm]
  rw [h1, dotProduct_mulVec, ← star_mulVec]
  exact hy _ (hpiS _ _ hz)

private theorem conj_mem {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p m : UJ ε} (hp : p ∈ parab ε W)
    (hm : m ∈ flagN ε W) : p⁻¹ * m * p ∈ flagN ε W := by
  have e : ∀ y, uMat (p⁻¹ * m * p) *ᵥ y - y = uMat p⁻¹ *ᵥ (uMat m *ᵥ (uMat p *ᵥ y) - uMat p *ᵥ y) := fun y => by
    rw [mulVec_sub, act_inv, act_mul, act_mul]
  have hi := (parab ε W).inv_mem hp
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [e]; exact hi _ _ (hm.1 i _ (hp _ y hy))
  · rw [e]; exact hi _ _ (hm.2 _ (keeps_perp hp hy))

private theorem comm_mem {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p t : UJ ε} {x : Fin a → ℝ}
    (hp : p ∈ parab ε W) (ht : IsSplit ε W x t) : t⁻¹ * (p * t * p⁻¹) ∈ flagN ε W := by
  have hpS : ∀ i, ∀ y ∈ W i, uMat p *ᵥ y ∈ W i := hp
  have hpiS : ∀ i, ∀ y ∈ W i, uMat p⁻¹ *ᵥ y ∈ W i := (parab ε W).inv_mem hp
  have htS : ∀ i, ∀ y ∈ W i, uMat t *ᵥ y ∈ W i := fun i y hy => (ht.1 i y hy).1
  have htiS : ∀ i, ∀ y ∈ W i, uMat t⁻¹ *ᵥ y ∈ W i :=
    (parab ε W).inv_mem (show t ∈ parab ε W from htS)
  simp only [flagN, Set.mem_setOf_eq]
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · have e : uMat (t⁻¹ * (p * t * p⁻¹)) *ᵥ y - y =
        uMat t⁻¹ *ᵥ (uMat p *ᵥ (uMat t *ᵥ (uMat p⁻¹ *ᵥ y) -
          (Real.exp (x i) : ℂ) • (uMat p⁻¹ *ᵥ y))) -
          uMat t⁻¹ *ᵥ (uMat t *ᵥ y - (Real.exp (x i) : ℂ) • y) := by
      simp only [act_mul, mulVec_sub, mulVec_smul, act_inv, act_inv']
      abel
    rw [e]
    exact Submodule.sub_mem _ (htiS _ _ (hpS _ _ (ht.2.1 i _ (hpiS _ _ hy))))
      (htiS _ _ (ht.2.1 i y hy))
  · have e : uMat (t⁻¹ * (p * t * p⁻¹)) *ᵥ y - y =
        uMat t⁻¹ *ᵥ (uMat p *ᵥ (uMat t *ᵥ (uMat p⁻¹ *ᵥ y) - uMat p⁻¹ *ᵥ y)) -
          uMat t⁻¹ *ᵥ (uMat t *ᵥ y - y) := by
      simp only [act_mul, mulVec_sub, act_inv, act_inv']
      abel
    rw [e]
    exact Submodule.sub_mem _
      (htiS _ _ (hpS _ _ (ht.2.2 _ (keeps_perp ((parab ε W).inv_mem hp) hy))))
      (htiS _ _ (ht.2.2 y hy))

theorem UpperTheory.Lit.Cusp.exists_isRay :
    ∀ (n : ℕ) (ε : Fin n → Bool) (j : Fin 1 → ℕ) (W : Flag n 1), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      ∃ (a : ℝ → UJ ε) (H : UJ ε → ℝ), IsRay (flagN ε W) a H := by
  intro n ε j W hW hj
  obtain ⟨a, ha_cont, ha_add, ha_split⟩ := exists_split n ε j W hW
  obtain ⟨h, hh_cont, hh1, hhK, hhP⟩ := exists_height hW hj
  obtain ⟨⟨N, hN⟩, -, -⟩ := UnipRad.flagN_subgroup_closed_keeps n ε 1 j W hW
  have hone_levi : (1 : UJ ε) ∈ leviOne ε W := (leviOne ε W).one_mem
  have hone_N : (1 : UJ ε) ∈ flagN ε W := hN ▸ N.one_mem
  have hN_inv : ∀ m ∈ flagN ε W, m⁻¹ ∈ flagN ε W := by
    intro m hm
    rw [← hN] at hm ⊢
    exact N.inv_mem hm
  have hsplit_par : ∀ t, a t ∈ parab ε W := fun t =>
    show ∀ i, ∀ y ∈ W i, uMat (a t) *ᵥ y ∈ W i from fun i y hy => ((ha_split t).1 i y hy).1
  have hheight : ∀ x t g, IsSplit ε W x t → h (t * g) = x + h g := by
    intro x t g hs
    have := hhP 1 hone_N 1 hone_levi x t hs g
    rwa [one_mul, one_mul] at this
  have ha0 : a 0 = 1 := by
    have h0 := congrArg (fun g => (a 0)⁻¹ * g) (ha_add 0 0)
    simp only [add_zero, inv_mul_cancel, ← mul_assoc, one_mul] at h0
    exact h0.symm
  have hainv : ∀ t, (a t)⁻¹ = a (-t) := fun t => by
    have h2 : a t * a (-t) = 1 := by rw [← ha_add, add_neg_cancel, ha0]
    exact (eq_inv_of_mul_eq_one_right h2).symm
  have hK : IsCompact (KG ε : Set (UJ ε)) := isCompact_iff_compactSpace.2 (instCompactKG n ε)
  have hkmem : ∀ k ∈ maxK ε, k ∈ KG ε := fun k hk => by
    rw [← SetLike.mem_coe, KG_eq]
    exact hk
  have hshift : ∀ y g : UJ ε, ∃ k ∈ KG ε, h (y * g) = h y + h (k * g) := by
    intro y g
    obtain ⟨k, hkK, hk⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW y
    obtain ⟨u, hu, m, hm, x, t, hs, hp⟩ := exists_langlands_decomp hW hj hk
    have hkG := hkmem k hkK
    refine ⟨k, hkG, ?_⟩
    have e1 : y * g = u * m * t * (k * g) := by
      rw [← hp]
      group
    have e2 : y = u * m * t * k := by
      rw [← hp]
      group
    have hk0 : h k = 0 := by
      have := hhK 1 k hkG
      rwa [one_mul, hh1] at this
    rw [e1, hhP u hu m hm x t hs, e2, hhP u hu m hm x t hs, hk0, add_zero]
  refine ⟨a, fun g => -(h g⁻¹ 0), ha_cont, ha_add, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t m hm
    exact conj_mem (hsplit_par t) hm
  · exact ((continuous_apply 0).comp (hh_cont.comp continuous_inv)).neg
  · intro g m hm
    show -(h (g * m)⁻¹ 0) = -(h g⁻¹ 0)
    have := hhP m⁻¹ (hN_inv m hm) 1 hone_levi 0 1 isSplit_one g⁻¹
    rw [mul_one, mul_one, zero_add] at this
    rw [_root_.mul_inv_rev, this]
  · intro g t
    show -(h (g * a t)⁻¹ 0) = -(h g⁻¹ 0) + t
    rw [_root_.mul_inv_rev, hainv, hheight _ _ _ (ha_split (-t))]
    simp only [Pi.add_apply]
    ring
  · intro D hD
    have hS : IsCompact ((fun q : UJ ε × UJ ε => q.1 * q.2) '' ((KG ε : Set (UJ ε)) ×ˢ D)) :=
      (hK.prod hD).image continuous_mul
    obtain ⟨c, hc⟩ := hS.exists_bound_of_continuousOn (f := fun g => h g 0)
      ((continuous_apply 0).comp hh_cont).continuousOn
    refine ⟨c, fun g hg x => ?_⟩
    obtain ⟨k, hk, hyg⟩ := hshift x⁻¹ g
    show |-(h (g⁻¹ * x)⁻¹ 0) - -(h x⁻¹ 0)| ≤ c
    rw [_root_.mul_inv_rev, _root_.inv_inv, hyg]
    have hb := hc (k * g) ⟨(k, g), ⟨hk, hg⟩, rfl⟩
    rw [Real.norm_eq_abs] at hb
    have e : -((h x⁻¹ + h (k * g)) 0) - -(h x⁻¹ 0) = -(h (k * g) 0) := by
      simp only [Pi.add_apply]
      ring
    rw [e, abs_neg]
    exact hb
  · refine ⟨(KG ε : Set (UJ ε)), hK, fun x => ?_⟩
    obtain ⟨k, hkK, hk⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW x⁻¹
    have hkG := hkmem k hkK
    refine ⟨k⁻¹, (KG ε).inv_mem hkG, fun t => ?_⟩
    have hq : x⁻¹ * k⁻¹ ∈ parab ε W := hk
    refine ⟨(a t)⁻¹ * ((x⁻¹ * k⁻¹) * a t * (x⁻¹ * k⁻¹)⁻¹), comm_mem hq (ha_split t), ?_⟩
    group
end
end
