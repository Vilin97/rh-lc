module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsGlueDataPre
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqOfCover
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SpanPowMulLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
import Mathlib.Analysis.CStarAlgebra.Classes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardFilterLtInj

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem card_filter_lt_inj {n : ℕ} (P : Finset (Fin n)) {i k : Fin n} (hi : i ∈ P) (hk : k ∈ P)
    (e : (P.filter (· < i)).card = (P.filter (· < k)).card) : i = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : (P.filter (· < i)).card < (P.filter (· < k)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hi, h⟩)
        simp at this
    omega
  · have : (P.filter (· < k)).card < (P.filter (· < i)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hk, h⟩)
        simp at this
    omega

theorem card_filter_lt_lt {n : ℕ} (P : Finset (Fin n)) {i : Fin n} (hi : i ∈ P) :
    (P.filter (· < i)).card < P.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, hi, lt_irrefl i⟩)

end Formalism.L2.SG.Pf.GluingBases
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPrescFamily

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem bin_step_gen (h : V →ₗ⋆[K] V →ₗ[K] K) (hz : ∀ x y, h x y = 0 → h y x = 0) (e₁ e₂ : V)
    (a b x y n : K) (h12 : h e₁ e₂ = 0) (h11 : h e₁ e₁ = a) (h22 : h e₂ e₂ = b) (ha : star a = a)
    (hb : star b = b) (hxy : a * (x * star x) + b * (y * star y) = n) :
    h (x • e₁ + y • e₂) (x • e₁ + y • e₂) = n ∧
      h (x • e₁ + y • e₂) ((star y * b) • e₁ - (star x * a) • e₂) = 0 ∧
      h ((star y * b) • e₁ - (star x * a) • e₂) ((star y * b) • e₁ - (star x * a) • e₂) =
        a * b * n := by
  have h21 : h e₂ e₁ = 0 := hz _ _ h12
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    linear_combination hxy
  · simp only [map_add (f := _), map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    ring
  · simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22, star_mul', star_star, ha, hb]
    linear_combination (a * b) * hxy

theorem TotPos.ne_zero' {x : K} (hx : TotPos x) : x ≠ 0 := by
  intro h0
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := hx φ
  rw [h0, map_zero] at this
  simp at this

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem exists_presc_family (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ x y, star (h x y) = h y x)
    (hpos : ∀ x, x ≠ 0 → TotPos (h x x)) :
    ∀ k : ℕ, k + 1 ≤ finrank K V → ∀ t : Fin (k + 1) → K, (∀ i, star (t i) = t i) →
      (∀ i, TotPos (t i)) →
      ∃ v : Fin (k + 1) → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        (∀ i, i ≠ Fin.last k → h (v i) (v i) = t i) ∧ v (Fin.last k) ≠ 0 := by
  have hz : ∀ x y, h x y = 0 → h y x = 0 := fun x y e => by rw [← hsym, e, star_zero]
  intro k
  induction k with
  | zero =>
    intro hk t _ _
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hsub : ∀ i j : Fin (0 + 1), i = j := fun i j => Fin.ext (by omega)
    exact ⟨fun _ => x, fun i j hij => absurd (hsub i j) hij,
      fun i hi => absurd (hsub i _) hi, hx⟩
  | succ k ih =>
    intro hk t hts htp
    obtain ⟨v, ho, h1, hl⟩ := ih (by omega) (fun i => t (Fin.castSucc i)) (fun i => hts _)
      (fun i => htp _)
    obtain ⟨z, hz0, hzv⟩ := GramDeterminantPositive.exists_ortho_ne_zero h v (by omega)
    obtain ⟨x, y, hxy⟩ := hermRepUnram K hK (h (v (Fin.last k)) (v (Fin.last k))) (h z z)
      (t (Fin.castSucc (Fin.last k))) (hsym _ _) (hsym _ _) (hts _) (hpos _ hl) (hpos _ hz0) (htp _)
    obtain ⟨b1, b2, b3⟩ := bin_step_gen h hz (v (Fin.last k)) z _ _ x y _ (hzv _) rfl rfl
      (hsym _ _) (hsym _ _) hxy
    set a := h (v (Fin.last k)) (v (Fin.last k)) with ha
    set b := h z z with hb
    set f₁ := x • v (Fin.last k) + y • z with hf₁
    set f₂ := (star y * b) • v (Fin.last k) - (star x * a) • z with hf₂
    have hf₂0 : f₂ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at b3
      exact mul_ne_zero (mul_ne_zero (TotPos.ne_zero' (hpos _ hl)) (TotPos.ne_zero' (hpos _ hz0)))
        (TotPos.ne_zero' (htp _)) b3.symm
    have c1 : ∀ i, i ≠ Fin.last k → h (v i) f₁ = 0 := by
      intro i hi
      rw [hf₁, map_add (f := _), map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, add_zero]
    have c2 : ∀ i, i ≠ Fin.last k → h (v i) f₂ = 0 := by
      intro i hi
      rw [hf₂, map_sub, map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, sub_zero]
    let u : Fin (k + 1) → V := Function.update v (Fin.last k) f₁
    have ul : u (Fin.last k) = f₁ := Function.update_self _ _ _
    have un : ∀ i, i ≠ Fin.last k → u i = v i := fun i hi => Function.update_of_ne hi _ _
    have uo : ∀ i j, i ≠ j → h (u i) (u j) = 0 := by
      intro i j hij
      by_cases hi : i = Fin.last k
      · have hj : j ≠ Fin.last k := fun e => hij (hi.trans e.symm)
        rw [hi, ul, un j hj]
        exact hz _ _ (c1 j hj)
      · by_cases hj : j = Fin.last k
        · rw [hj, ul, un i hi]; exact c1 i hi
        · rw [un i hi, un j hj]; exact ho i j hij
    have u1 : ∀ i, h (u i) (u i) = t (Fin.castSucc i) := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b1
      · rw [un i hi]; exact h1 i hi
    have u2 : ∀ i, h (u i) f₂ = 0 := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b2
      · rw [un i hi]; exact c2 i hi
    refine ⟨Fin.snoc u f₂, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hz _ _ (u2 j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact u2 i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact uo i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hi; exact absurd rfl hi
      · intro _
        rw [Fin.snoc_castSucc]; exact u1 i
    · rw [Fin.snoc_last]; exact hf₂0

end Formalism.L2.SG.Pf.GluingBases
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsTotPosCongr

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_totPos_congr {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hne : 𝔭 ≠ ⊥) (a : 𝓞 F) (k : ℕ) :
    ∃ x : F, TotPos (algebraMap F K x) ∧ InP 𝔭 k (algebraMap F K ((a : F) + x)) := by
  have := h𝔭.isPrime
  have ht0 : Ideal.absNorm (𝔭 ^ k) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact pow_ne_zero _ hne
  have htm : ((Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := Ideal.absNorm_mem _
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ φ : K →+* ℂ, ‖φ (algebraMap F K (a : F))‖)
  have hz : ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ htm
  have hzF : (((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) = ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : F) := by
    simp
  refine ⟨(((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) - (a : F), ?_, ?_⟩
  · intro φ
    rw [hzF, map_sub, map_sub, map_natCast, map_natCast, Complex.sub_re, Complex.natCast_re]
    have h1 : (φ (algebraMap F K (a : F))).re ≤ ∑ ψ : K →+* ℂ, ‖ψ (algebraMap F K (a : F))‖ :=
      (Complex.re_le_norm _).trans (Finset.single_le_sum
        (f := fun ψ : K →+* ℂ => ‖ψ (algebraMap F K (a : F))‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ φ))
    have h2 : (N : ℝ) ≤ ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_right (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht0)
    linarith
  · rw [add_sub_cancel]
    exact inP_of_mem_pow hz

end Formalism.L2.SG.Pf.GluingBases
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingVectorsExist

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem gluing_vectors_exist : GlueVecsPre := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  have := h𝔭.isPrime
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  set W := orthK h U with hW
  set m := finrank K W with hm
  set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  have hPc : P.card < m := hc
  have hPm : ∀ i, (P.filter (· < i)).card < m := fun i =>
    lt_of_le_of_lt (Finset.card_filter_le _ _) hPc
  let τ : Fin (finrank K U) → Fin m := fun i => ⟨(P.filter (· < i)).card, hPm i⟩
  have hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k := by
    intro i k hi hk e
    exact card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)
  have hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m := by
    intro i hi
    have := card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    show (P.filter (· < i)).card + 1 < m
    omega
  choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))
  let t : Fin m → K := fun j =>
    if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1
  have hts : ∀ j, star (t j) = t j := by
    intro j; simp only [t]; split_ifs
    · exact star_fix hF _
    · exact star_one K
  have htp : ∀ j, TotPos (t j) := by
    intro j; simp only [t]; split_ifs
    · exact hnpos _
    · intro φ; rw [map_one]; simp
  have htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i) := by
    intro i hi
    have hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i := ⟨i, hi, rfl⟩
    simp only [t, dif_pos hj]
    rw [hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]
  have htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1 := by
    intro j hj
    have : ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j := fun ⟨i, hi, e⟩ => hj i hi e
    simp only [t, dif_neg this]
  let h' : W →ₗ⋆[K] W →ₗ[K] K := (LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)
  have h'a : ∀ x y : W, h' x y = h x y := fun x y => rfl
  have hsym' : ∀ x y : W, star (h' x y) = h' y x := by
    intro x y; rw [h'a, h'a, ← starRingEnd_apply]; exact hs.eq _ _
  have hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x) := by
    intro x hx φ; rw [h'a]; exact hpos x x.2 (fun e => hx (Subtype.ext e)) φ
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨v, ho, hv1, hvl⟩ := exists_presc_family hK h' hsym' hpos' (m - 1) (by omega)
    (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)
  let w : Fin m → V := fun j => (v (Fin.cast hm1.symm j) : V)
  have hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0 := by
    intro j k hjk
    exact ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))
  have hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j := by
    intro j hj
    have hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have := hv1 _ hne'
    simpa [w, h'a] using this
  have hwn0 : ∀ j, h (w j) (w j) ≠ 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < m
    · rw [hwn j hj]; exact TotPos.ne_zero' (htp j)
    · have hjl := j.isLt
      have hl : Fin.cast hm1.symm j = Fin.last (m - 1) := by
        ext; simp; omega
      have : v (Fin.cast hm1.symm j) ≠ 0 := by rw [hl]; exact hvl
      exact TotPos.ne_zero' (hpos' _ this)
  have hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x := fun j => by
    obtain ⟨x, hx⟩ := (hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))
    exact ⟨x, hx.symm⟩
  choose c hcw using hfix
  obtain ⟨π, s₀, hu⟩ := exists_isUnif0 h𝔭
  refine ⟨π, w, c, τ, fun j => (v _).2, hwo,
    fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩
  · intro i hi
    have e : algebraMap F K (c (τ i)) = algebraMap F K (nF i) := by
      rw [← hcw, hwn _ (hτl i hi), htpart i hi]
    rw [(algebraMap F K).injective e]
    exact hncong i
  · intro j hj hnp
    have e : c j = 1 := by
      apply (algebraMap F K).injective
      rw [← hcw, hwn j hj, htnp j hnp, map_one]
    rw [e, inv_one, map_one]
    exact ⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩

end Formalism.L2.SG.Pf.GluingBases
end
end
end
