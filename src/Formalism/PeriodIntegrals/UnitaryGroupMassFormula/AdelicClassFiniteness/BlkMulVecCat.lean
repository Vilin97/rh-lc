module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSingleLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SplHformZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartBetween

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem partBetween : PartBetween := by
  intro E _ _ m N hN δ hδ
  obtain ⟨k, n, hn⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN
  have hne : Ideal.span {δ} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : Finite ((𝓞 E) ⧸ Ideal.span {δ}) := by
    first
      | exact (Ideal.absNorm_ne_zero_iff _).mp (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)
      | exact Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hδE : algebraMap (𝓞 E) E δ ≠ 0 := by
    intro h
    apply hδ
    exact IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero])
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {δ}))
  let T : Set (Fin m → E) := Set.range (fun c : Fin k → ((𝓞 E) ⧸ Ideal.span {δ}) =>
    (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E (g (c i))) • n i)
  have hT : T.Finite := Set.finite_range _
  have key : ∀ x : Fin m → E, δ • x ∈ N → ∃ t ∈ T, x - t ∈ N := by
    intro x hx
    rw [← hn] at hx
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hx
    have hq : ∀ i, ∃ q : 𝓞 E, algebraMap (𝓞 E) E (a i) -
        algebraMap (𝓞 E) E (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i))) =
        algebraMap (𝓞 E) E δ * algebraMap (𝓞 E) E q := by
      intro i
      have h := Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {δ}))
        (Ideal.Quotient.mk (Ideal.span {δ}) (a i))
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      refine ⟨-c, ?_⟩
      rw [← map_sub, ← map_mul, mul_neg, ← hc, neg_sub]
    choose q hq using hq
    refine ⟨_, ⟨fun i => Ideal.Quotient.mk (Ideal.span {δ}) (a i), rfl⟩, ?_⟩
    have hx2 : x = (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, a i • n i := by
      rw [ha, ← algebraMap_smul E δ x, smul_smul, inv_mul_cancel₀ hδE, one_smul]
    have e1 : ∀ i, a i • n i - (algebraMap (𝓞 E) E (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i =
        (algebraMap (𝓞 E) E δ) • (q i • n i) := by
      intro i
      rw [← algebraMap_smul E (a i), ← algebraMap_smul E (q i), smul_smul, ← sub_smul, hq i]
    have hdiff : x - (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E
        (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i = ∑ i, q i • n i := by
      rw [hx2, ← smul_sub, ← Finset.sum_sub_distrib]
      simp_rw [e1]
      rw [← Finset.smul_sum, smul_smul, inv_mul_cancel₀ hδE, one_smul]
    show x - (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E
        (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i ∈ N
    rw [hdiff, ← hn]
    exact (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mpr ⟨q, rfl⟩
  apply Set.Finite.subset (hT.powerset.image (fun S => N ⊔ Submodule.span (𝓞 E) S))
  intro M hM
  obtain ⟨hNM, hMδ⟩ := hM
  refine ⟨(M : Set (Fin m → E)) ∩ T, Set.inter_subset_right, ?_⟩
  apply le_antisymm
  · exact sup_le hNM (Submodule.span_le.mpr Set.inter_subset_left)
  · intro x hx
    obtain ⟨t, htT, hxt⟩ := key x (hMδ x hx)
    have htM : t ∈ M := by
      have h := M.sub_mem hx (hNM hxt)
      rwa [sub_sub_cancel] at h
    have e : x = (x - t) + t := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hxt)
      (Submodule.mem_sup_right (Submodule.subset_span ⟨htM, htT⟩))

end PIW.AdelClassFin
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SpComp

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open scoped Matrix

theorem spComp : SpComp := by
  intro E _ k m P R hPR
  have hsurj : Function.Surjective (Matrix.toLin' P) := fun v =>
    ⟨R *ᵥ v, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hPR, Matrix.one_mulVec]⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' P)
  have hrank : Module.finrank E (LinearMap.range (Matrix.toLin' P)) = k := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]
  rw [hrank, Module.finrank_fin_fun] at hsum
  have hker : Module.finrank E (LinearMap.ker (Matrix.toLin' P)) = m - k := by omega
  refine ⟨by omega, ?_⟩
  let b : Module.Basis (Fin (m - k)) E (LinearMap.ker (Matrix.toLin' P)) := Module.finBasisOfFinrankEq E _ hker
  have hU : ∀ y : Fin (m - k) → E,
      (Matrix.of fun i j => (b j : Fin m → E) i) *ᵥ y =
        ((b.equivFun.symm y : LinearMap.ker (Matrix.toLin' P)) : Fin m → E) := by
    intro y
    ext i
    rw [Module.Basis.equivFun_symm_apply]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨Matrix.of fun i j => (b j : Fin m → E) i, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (LinearMap.mem_ker.mp (b j).2) i
    rw [Matrix.toLin'_apply] at h
    exact h
  · intro y y' h
    simp only [hU] at h
    exact b.equivFun.symm.injective (Subtype.ext h)
  · intro w hw
    refine ⟨b.equivFun ⟨w, LinearMap.mem_ker.mpr (by rw [Matrix.toLin'_apply]; exact hw)⟩, ?_⟩
    rw [hU, LinearEquiv.symm_apply_apply]

end PIW.AdelClassFin
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SpDen

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem spDen : SpDen := by
  intro E _ _ k X
  have h : ∀ p : Fin k × Fin k, ∃ D : ℕ, 1 ≤ D ∧ (D : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range := by
    intro p
    obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ (X p.1 p.2)))
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    have hmem : (y : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range :=
      ⟨⟨(y : E) * X p.1 p.2, by rw [mem_integralClosure_iff]; simpa [zsmul_eq_mul] using hint⟩, rfl⟩
    have h2 : (y.natAbs : ℤ) = y ∨ (y.natAbs : ℤ) = -y := by
      rcases Int.natAbs_eq y with h | h
      · exact Or.inl h.symm
      · right; linarith
    rw [← Int.cast_natCast]
    rcases h2 with h2 | h2 <;> rw [h2]
    · exact hmem
    · rw [Int.cast_neg, neg_mul]; exact neg_mem hmem
  choose Dp hDp1 hDp using h
  refine ⟨∏ p, Dp p, Finset.one_le_prod' fun p _ => hDp1 p, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Dp (Finset.mem_univ (i, j))
  rw [hc, Nat.cast_mul, mul_comm (Dp (i, j) : E), mul_assoc]
  exact Subring.mul_mem _ ⟨c, by simp⟩ (hDp (i, j))

end PIW.AdelClassFin
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.BlkMulVecCat

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

namespace SpO

def cat {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (c : Fin k → E) (y : Fin n → E) :
    Fin m → E :=
  fun r => Sum.elim c y (e.symm r)

def blk {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (V : Matrix (Fin m) (Fin k) E)
    (W : Matrix (Fin m) (Fin n) E) : Matrix (Fin m) (Fin m) E :=
  Matrix.of fun r s => Sum.elim (fun i => V r i) (fun j => W r j) (e.symm s)

def catR {E : Type} [Field E] (R : Type) [CommRing R] [Algebra R E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) :
    (Fin n → E) →ₗ[R] (Fin m → E) where
  toFun y := cat e 0 y
  map_add' y y' := by
    funext r
    simp only [cat, Pi.add_apply]
    cases e.symm r <;> simp
  map_smul' a y := by
    funext r
    simp only [cat, Pi.smul_apply, RingHom.id_apply]
    cases e.symm r <;> simp

theorem catR_apply {E : Type} [Field E] (R : Type) [CommRing R] [Algebra R E] {m k n : ℕ}
    (e : Fin k ⊕ Fin n ≃ Fin m) (y : Fin n → E) : catR R e y = cat e 0 y := rfl

theorem cat_add {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (c : Fin k → E) (y : Fin n → E) :
    cat e c 0 + cat e 0 y = cat e c y := by
  funext r
  simp only [cat, Pi.add_apply]
  cases e.symm r <;> simp

theorem blk_mulVec {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (V : Matrix (Fin m) (Fin k) E)
    (W : Matrix (Fin m) (Fin n) E) (x : Fin m → E) :
    blk e V W *ᵥ x = V *ᵥ (fun i => x (e (Sum.inl i))) + W *ᵥ (fun j => x (e (Sum.inr j))) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.of_apply, Pi.add_apply]
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp

theorem blk_mulVec_cat {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (V : Matrix (Fin m) (Fin k) E)
    (W : Matrix (Fin m) (Fin n) E) (c : Fin k → E) (y : Fin n → E) :
    blk e V W *ᵥ cat e c y = V *ᵥ c + W *ᵥ y := by
  rw [blk_mulVec]
  simp [cat]

theorem single_inl {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (i : Fin k) :
    (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E) = cat e (Pi.single i 1) 0 := by
  funext r
  obtain ⟨t, rfl⟩ := e.surjective r
  cases t with
  | inl a => simp [cat, Pi.single_apply, e.injective.eq_iff]
  | inr b => simp [cat, Pi.single_apply, e.injective.eq_iff]

theorem single_inr {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (j : Fin n) :
    (Pi.single (e (Sum.inr j)) (1 : E) : Fin m → E) = cat e 0 (Pi.single j 1) := by
  funext r
  obtain ⟨t, rfl⟩ := e.surjective r
  cases t with
  | inl a => simp [cat, Pi.single_apply, e.injective.eq_iff]
  | inr b => simp [cat, Pi.single_apply, e.injective.eq_iff]

theorem cat_eq_sum {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (c : Fin k → E) :
    cat e c 0 = ∑ i, c i • (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E) := by
  funext r
  obtain ⟨t, rfl⟩ := e.surjective r
  cases t with
  | inl a => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]
  | inr b => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]

theorem entry_eq {E : Type} [Field E] [StarRing E] {m : ℕ} (J A : Matrix (Fin m) (Fin m) E) (r s : Fin m) :
    (cT (starRingEnd E) A * J * A) r s =
      hform (starRingEnd E) J (A *ᵥ Pi.single r 1) (A *ᵥ Pi.single s 1) := by
  simp only [cT, hform, Matrix.mul_apply, Matrix.mulVec_single_one, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

end SpO

open SpO in
theorem spOne : SpOne := by
  intro E _ _ _ m k hk ih d hd Γ hΓ
  classical
  by_cases hkm : k ≤ m
  swap
  · refine ⟨∅, Set.finite_empty, ?_⟩
    rintro p ⟨_, v, _, hvΓ⟩
    exfalso
    apply hkm
    have hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ :=
      (gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)
    refine (spComp E k m (cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1)
      ((Matrix.of fun r i => v i r) * Γ⁻¹) ?_).1
    rw [← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]
  obtain ⟨D, hD1, hDΓ⟩ := spDen E k Γ⁻¹
  have hnm : m - k < m := by omega
  have hdD : 1 ≤ d * D := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨T', hT'f, hT'⟩ := ih (m - k) hnm (d * D) hdD
  let e : Fin k ⊕ Fin (m - k) ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega))
  let N : Submodule (𝓞 E) (Fin (m - k) → E) → Submodule (𝓞 E) (Fin m → E) := fun M' =>
    Submodule.span (𝓞 E) (Set.range fun i : Fin k => (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E)) ⊔
      M'.map (catR (𝓞 E) e)
  let Jb : Matrix (Fin (m - k)) (Fin (m - k)) E → Matrix (Fin m) (Fin m) E := fun J' =>
    Matrix.of fun r s => Matrix.fromBlocks Γ 0 0 J' (e.symm r) (e.symm s)
  let T : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) :=
    ⋃ q' ∈ {q' | q' ∈ T' ∧ q'.2.FG}, (fun M₀ => (Jb q'.1, M₀)) ''
      {M₀ : Submodule (𝓞 E) (Fin m → E) | N q'.2 ≤ M₀ ∧ ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2}
  have hD0 : (D : 𝓞 E) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 E) E) h0
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h1
    omega
  refine ⟨T, ?_, ?_⟩
  · refine Set.Finite.biUnion (hT'f.subset (by exact fun q h => h.1)) fun q' hq' => ?_
    refine Set.Finite.image _ (partBetween E m (N q'.2) ?_ (D : 𝓞 E) hD0)
    exact (Submodule.fg_span (Set.finite_range _)).sup (hq'.2.map _)
  rintro p ⟨hp, v, hv, hvΓ⟩
  have hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ :=
    (gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)
  set V : Matrix (Fin m) (Fin k) E := Matrix.of fun r i => v i r with hVdef
  have hPR : (cT (starRingEnd E) V * p.1) * (V * Γ⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]
  obtain ⟨-, U, hPU, hUinj, hUsurj⟩ := spComp E k m _ _ hPR
  have hVM : ∀ i, (fun r => V r i) ∈ p.2 := fun i => hv i
  obtain ⟨hLat', hdec⟩ := spLat E m k (m - k) d D p.1 p.2 V U hp hVM hD1 (by rw [hg]; exact hΓ)
    (by rw [hg]; exact hDΓ) hPU hUinj hUsurj
  obtain ⟨q', hq', B, hB1, hB2⟩ := hT' _ hLat'
  set W : Matrix (Fin m) (Fin (m - k)) E := U * (B : Matrix (Fin (m - k)) (Fin (m - k)) E) with hWdef
  set A : Matrix (Fin m) (Fin m) E := blk e V W with hAdef
  have hJh : p.1ᴴ = p.1 := (isHerm_iff _).1 hp.1
  have hUV : cT (starRingEnd E) U * p.1 * V = 0 := by
    have h := congrArg Matrix.conjTranspose hPU
    rw [cT_star] at h ⊢
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at h
    exact h
  have hPW : cT (starRingEnd E) V * p.1 * W = 0 := by
    rw [hWdef, ← Matrix.mul_assoc, hPU, Matrix.zero_mul]
  have hWy : ∀ y, W *ᵥ y = U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y) := fun y => by
    rw [hWdef, Matrix.mulVec_mulVec]
  have hker : ∀ x, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hAdef, blk_mulVec] at hx
    have h1 := congrArg (fun z => (cT (starRingEnd E) V * p.1) *ᵥ z) hx
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hg, hPW, Matrix.zero_mulVec, add_zero,
      Matrix.mulVec_zero] at h1
    have hΓu : IsUnit Γ := (Matrix.isUnit_iff_isUnit_det Γ).mpr (isUnit_iff_ne_zero.mpr hΓ)
    have hc0 : (fun i => x (e (Sum.inl i))) = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr hΓu (by rw [h1, Matrix.mulVec_zero])
    rw [hc0, Matrix.mulVec_zero, zero_add, hWy] at hx
    have hBy : (B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ (fun j => x (e (Sum.inr j))) = 0 :=
      hUinj (by rw [hx, Matrix.mulVec_zero])
    have hy0 : (fun j => x (e (Sum.inr j))) = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit B) (by rw [hBy, Matrix.mulVec_zero])
    funext r
    obtain ⟨t, rfl⟩ := e.surjective r
    cases t with
    | inl i => exact congrFun hc0 i
    | inr j => exact congrFun hy0 j
  have hAinj : Function.Injective A.mulVec := by
    intro x x' h
    have := hker (x - x') (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  have hdetA : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hAinj)).ne_zero
  set A' : GL (Fin m) E := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA with hA'def
  have hA'v : (A' : Matrix (Fin m) (Fin m) E) = A := rfl
  have hAcat : ∀ c y, A *ᵥ cat e c y = V *ᵥ c + U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y) := by
    intro c y
    rw [hAdef, blk_mulVec_cat, hWy]
  have hcol1 : ∀ i, A *ᵥ Pi.single (e (Sum.inl i)) 1 = V *ᵥ Pi.single i 1 := fun i => by
    rw [single_inl, hAcat, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  have hcol2 : ∀ j, A *ᵥ Pi.single (e (Sum.inr j)) 1 =
      U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ Pi.single j 1) := fun j => by
    rw [single_inr, hAcat, Matrix.mulVec_zero, zero_add]
  set M₀ : Submodule (𝓞 E) (Fin m → E) := p.2.comap (A.mulVecLin.restrictScalars (𝓞 E)) with hM₀
  have hmem : ∀ x, x ∈ M₀ ↔ A *ᵥ x ∈ p.2 := fun x => Iff.rfl
  have hfg' : q'.2.FG := by
    have heq : q'.2 = (p.2.comap (U.mulVecLin.restrictScalars (𝓞 E))).map
        (((B⁻¹ : GL (Fin (m - k)) E) : Matrix (Fin (m - k)) (Fin (m - k)) E).mulVecLin.restrictScalars (𝓞 E)) := by
      ext w
      simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
      constructor
      · intro hw
        refine ⟨(B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ w, (hB2 _).2 ⟨w, hw, rfl⟩, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨w, hw, rfl⟩ := (hB2 u).1 hu
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        exact hw
    rw [heq]
    exact hLat'.2.2.1.map _
  have hNle : N q'.2 ≤ M₀ := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hmem, hcol1, Matrix.mulVec_single_one]
      exact hv i
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap, catR_apply, hmem, hAcat, Matrix.mulVec_zero, zero_add]
      exact (hB2 _).2 ⟨y, hy, rfl⟩
  have hDN : ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2 := by
    intro x hx
    obtain ⟨c, hc, y', hy'M, hdecx⟩ := hdec _ ((hmem x).1 hx)
    obtain ⟨y0, hy0, hBy0⟩ := (hB2 y').1 hy'M
    have hxe : (D : 𝓞 E) • x = cat e c 0 + catR (𝓞 E) e y0 := by
      apply hAinj
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, Matrix.mulVec_smul, hdecx, catR_apply,
        cat_add, hAcat, hBy0]
    rw [hxe]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy0))
    rw [cat_eq_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hc i
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Jb q'.1, M₀), Set.mem_biUnion (x := q') ⟨hq', hfg'⟩ (Set.mem_image_of_mem _ ⟨hNle, hDN⟩), A', ?_, ?_⟩
  · show cT (starRingEnd E) (A' : Matrix (Fin m) (Fin m) E) * p.1 * (A' : Matrix (Fin m) (Fin m) E) = Jb q'.1
    rw [hA'v]
    ext r s
    obtain ⟨t, rfl⟩ := e.surjective r
    obtain ⟨t', rfl⟩ := e.surjective s
    rw [entry_eq]
    simp only [Jb, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases t with i | j <;> rcases t' with i' | j'
    · rw [hcol1, hcol1, hform_mulVec, hg, hform_single, Matrix.fromBlocks_apply₁₁]
    · rw [hcol1, hcol2, spl_cross p.1 V U hPU, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    · rw [hcol2, hcol1, spl_cross p.1 U V hUV, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · rw [hcol2, hcol2, hform_mulVec, hform_mulVec, hB1, hform_single, Matrix.fromBlocks_apply₂₂]
  · intro w
    constructor
    · intro hw
      refine ⟨((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w, ?_, ?_⟩
      · show A *ᵥ (((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w) ∈ p.2
        rw [← hA'v, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hw
      · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    · rintro ⟨u, hu, rfl⟩
      rw [hA'v]
      exact hu

end PIW.AdelClassFin
end
end
end
