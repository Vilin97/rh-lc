module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGramDetSandwich
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LoewnerDetBound

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem add_mul_eigenvalue_nonneg {M : Matrix n n ℂ} (hM : M.IsHermitian) {a b : ℝ}
    (h : ((a : ℂ) • (1 : Matrix n n ℂ) + (b : ℂ) • M).PosSemidef) (i : n) :
    0 ≤ a + b * hM.eigenvalues i := by
  set v : n → ℂ := ⇑(hM.eigenvectorBasis i) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := hM.eigenvectorBasis.orthonormal.ne_zero i
    apply h1
    ext j
    simpa [hv] using congrFun h0 j
  have hMv : M *ᵥ v = (hM.eigenvalues i : ℂ) • v := hM.mulVec_eigenvectorBasis i
  have h0 := h.dotProduct_mulVec_nonneg v
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hMv, smul_smul, ← add_smul,
    dotProduct_smul, smul_eq_mul] at h0
  have hs : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hv0
  have hx : ((a : ℂ) + (b : ℂ) * (hM.eigenvalues i : ℂ)) = ((a + b * hM.eigenvalues i : ℝ) : ℂ) := by
    push_cast; ring
  rw [hx] at h0
  have h2 := (Complex.nonneg_iff.mp h0).1
  rw [Complex.re_ofReal_mul] at h2
  exact (mul_nonneg_iff_of_pos_right (Complex.pos_iff.mp hs).1).mp h2

theorem norm_det_le_of_loewner {H A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : ((c : ℂ) • A - H).PosSemidef) (h₂ : ((c : ℂ) • A + H).PosSemidef) :
    0 ≤ A.det.re ∧ A.det.im = 0 ∧ ‖H.det‖ ≤ c ^ Fintype.card n * A.det.re := by
  have hA : A.PosSemidef := by
    have e : A = ((1 / (2 * c) : ℝ) : ℂ) • (((c : ℂ) • A + H) + ((c : ℂ) • A - H)) := by
      rw [show ((c : ℂ) • A + H) + ((c : ℂ) • A - H) = ((2 * c : ℝ) : ℂ) • A by
        push_cast; rw [mul_smul, two_smul]; abel, smul_smul, ← Complex.ofReal_mul,
        one_div_mul_cancel (by positivity), Complex.ofReal_one, one_smul]
    rw [e]
    exact (h₂.add h₁).smul (Complex.zero_le_real.mpr (by positivity))
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hA.det_nonneg
  refine ⟨hre, him.symm, ?_⟩
  by_cases h0 : A.det = 0
  · obtain ⟨v, hv0, hAv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have e1 : star v ⬝ᵥ (((c : ℂ) • A - H) *ᵥ v) = -(star v ⬝ᵥ (H *ᵥ v)) := by
      rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, dotProduct_neg]
    have e2 : star v ⬝ᵥ (((c : ℂ) • A + H) *ᵥ v) = star v ⬝ᵥ (H *ᵥ v) := by
      rw [add_mulVec, smul_mulVec, hAv, smul_zero, zero_add]
    have p1 := h₁.dotProduct_mulVec_nonneg v
    have p2 := h₂.dotProduct_mulVec_nonneg v
    rw [e1] at p1
    rw [e2] at p2
    have hz : star v ⬝ᵥ (H *ᵥ v) = 0 := le_antisymm (neg_nonneg.mp p1) p2
    have hw := (h₁.dotProduct_mulVec_zero_iff).mp (by rw [e1, hz, neg_zero])
    rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, neg_eq_zero] at hw
    rw [exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hw⟩, norm_zero]
    exact mul_nonneg (pow_nonneg hc.le _) hre
  · obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    rw [star_eq_conjTranspose] at hL
    have hLu : IsUnit L.det := isUnit_iff_ne_zero.mpr fun hl => h0 (by rw [hL, det_mul, hl, mul_zero])
    have hLHu : IsUnit Lᴴ.det := by
      rw [det_conjTranspose]
      exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hLu))
    set M := (L⁻¹)ᴴ * H * L⁻¹ with hMdef
    have hHM : H = Lᴴ * M * L := by
      rw [hMdef, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu,
        Matrix.mul_one]
    have hA1 : (L⁻¹)ᴴ * A * L⁻¹ = 1 := by
      rw [hL, conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Lᴴ)⁻¹ Lᴴ L,
        Matrix.nonsing_inv_mul _ hLHu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hLu]
    have hconj : ∀ s : ℝ, (L⁻¹)ᴴ * ((c : ℂ) • A + (s : ℂ) • H) * L⁻¹ = (c : ℂ) • 1 + (s : ℂ) • M := by
      intro s
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        hA1, hMdef]
    have hP : ∀ s : ℝ, s = 1 ∨ s = -1 → ((c : ℂ) • (1 : Matrix n n ℂ) + (s : ℂ) • M).PosSemidef := by
      rintro s (rfl | rfl)
      · rw [← hconj]
        simpa using h₂.conjTranspose_mul_mul_same L⁻¹
      · rw [← hconj]
        have e : (c : ℂ) • A + ((-1 : ℝ) : ℂ) • H = (c : ℂ) • A - H := by
          push_cast; rw [neg_one_smul, ← sub_eq_add_neg]
        rw [e]
        exact h₁.conjTranspose_mul_mul_same L⁻¹
    have hM : M.IsHermitian := by
      have h3 := (hP 1 (Or.inl rfl)).isHermitian
      rw [IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one] at h3
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_one, map_one, one_smul] at h3
      exact add_left_cancel h3
    have hb : ∀ i, |hM.eigenvalues i| ≤ c := fun i => by
      have u := add_mul_eigenvalue_nonneg hM (hP 1 (Or.inl rfl)) i
      have l := add_mul_eigenvalue_nonneg hM (hP (-1) (Or.inr rfl)) i
      rw [abs_le]
      constructor <;> linarith
    have hdA : A.det = Lᴴ.det * L.det := by rw [hL, det_mul]
    have hnA : ‖A.det‖ = A.det.re := by
      rw [← Complex.re_add_im A.det, ← him]
      simp [Complex.norm_real, abs_of_nonneg hre]
    have hdH : ‖H.det‖ = ‖M.det‖ * ‖A.det‖ := by
      rw [hHM, det_mul, det_mul, hdA]
      simp only [norm_mul]
      ring
    have hdM : ‖M.det‖ ≤ c ^ Fintype.card n := by
      rw [hM.det_eq_prod_eigenvalues, norm_prod]
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_).trans_eq
        (by rw [Finset.prod_const, Finset.card_univ] : ∏ _i : n, c = c ^ Fintype.card n)
      have := hb i
      rwa [RCLike.norm_ofReal]
    rw [hdH, ← hnA]
    exact mul_le_mul_of_nonneg_right hdM (norm_nonneg _)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.SubmatrixGram

section

@[expose] public section

open Matrix Filter Topology Asymptotics
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements
open scoped ComplexOrder

namespace LevelTowerAlt.MuBd

section Mat

theorem norm_entry_le {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.PosSemidef) {c : ℝ}
    (hc : ((c : ℂ) • (1 : Matrix n n ℂ) - H).PosSemidef) (p q : n) : ‖H p q‖ ≤ c := by
  have hd : ∀ i, 0 ≤ (H i i).re ∧ (H i i).im = 0 ∧ (H i i).re ≤ c := fun i => by
    have h1 := Complex.nonneg_iff.1 (hH.diag_nonneg (i := i))
    have h2 := (Complex.nonneg_iff.1 (hc.diag_nonneg (i := i))).1
    simp only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Complex.sub_re,
      Complex.ofReal_re] at h2
    exact ⟨h1.1, h1.2.symm, by linarith⟩
  have h2 := (Complex.nonneg_iff.1 (hH.submatrix ![p, q]).det_nonneg).1
  rw [det_fin_two] at h2
  simp only [submatrix_apply, cons_val_zero, cons_val_one] at h2
  have e : H q p = starRingEnd ℂ (H p q) := (hH.1.apply q p).symm
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    (hd p).2.1, zero_mul, sub_zero] at h2
  have h3 : (H p p).re * (H q q).re ≤ c * c := mul_le_mul (hd p).2.2 (hd q).2.2 (hd q).1 ((hd p).1.trans (hd p).2.2)
  exact abs_le_of_sq_le_sq' (by nlinarith) ((hd p).1.trans (hd p).2.2) |>.2

theorem quotNormSq_le {j N : ℕ} (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) :
    quotNormSq hj G ≤ (G.submatrix (tailIdx hj) (tailIdx hj)).det.re := by
  let e : Fin j ⊕ Fin (N - j) ≃ Fin N := finSumFinEquiv.trans (finCongr (by omega))
  have el : ∀ a, e (Sum.inl a) = headIdx hj a := fun a => by ext; simp [e, headIdx]
  have er : ∀ k, e (Sum.inr k) = tailIdx hj k := fun k => by ext; simp [e, tailIdx]
  set A := G.submatrix (headIdx hj) (headIdx hj) with hA
  set B := G.submatrix (headIdx hj) (tailIdx hj) with hB
  set D := G.submatrix (tailIdx hj) (tailIdx hj) with hD
  have hb : G.submatrix e e = fromBlocks A B Bᴴ D := by
    ext (a | a) (b | b) <;> simp [el, er, hA, hB, hD]
    exact (hG.1.apply _ _).symm
  have hAp : A.PosDef := hG.submatrix (Fin.castLE_injective hj)
  have hDp : D.PosSemidef := hG.posSemidef.submatrix _
  letI : Invertible A := hAp.isUnit.invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef := (PosDef.fromBlocks₁₁ B D hAp).1 (hb ▸ hG.posSemidef.submatrix e)
  have hT : (Bᴴ * A⁻¹ * B).PosSemidef := hAp.inv.posSemidef.conjTranspose_mul_mul_same B
  have hdet : G.det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [← det_submatrix_equiv_self e, hb, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have h1 := (norm_det_le_of_loewner (H := D - Bᴴ * A⁻¹ * B) (A := D) one_pos
    (by simpa using hT) (by simpa using hDp.add hS)).2.2
  have h2 := Complex.pos_iff.1 hAp.det_pos
  unfold quotNormSq
  rw [← hA, hdet, Complex.mul_re, ← h2.2, zero_mul, sub_zero, mul_div_cancel_left₀ _ h2.1.ne']
  exact (Complex.re_le_norm _).trans (by simpa using h1)

theorem submatrix_gram' {N k : ℕ} (A H : Matrix (Fin N) (Fin N) ℂ) (e : Fin k → Fin N) :
    (Aᴴ * H * A).submatrix e e = (A.submatrix id e)ᴴ * H * A.submatrix id e := by
  ext a b
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

end Mat

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

structure Gr {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (l : Filter V) (L E : V → ℝ) (f : V → F) : Prop where
  diff : ∀ᶠ t in l, DifferentiableAt ℝ f t
  bdd : f =O[l] L
  der : fderiv ℝ f =O[l] E

variable {l : Filter V} {L E : V → ℝ}

section Gen

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Gr.zero : Gr l L E (fun _ => (0 : F)) :=
  ⟨Eventually.of_forall fun _ => differentiableAt_const _, isBigO_zero _ _, by
    rw [fderiv_fun_const]; exact isBigO_zero _ _⟩

theorem Gr.add {f g : V → F} (hf : Gr l L E f) (hg : Gr l L E g) : Gr l L E fun t => f t + g t := by
  refine ⟨(hf.diff.and hg.diff).mono fun t h => h.1.fun_add h.2, hf.bdd.add hg.bdd,
    (hf.der.add hg.der).congr' ?_ EventuallyEq.rfl⟩
  filter_upwards [hf.diff, hg.diff] with t h1 h2
  rw [fderiv_fun_add h1 h2]

theorem Gr.sum {σ : Type} (s : Finset σ) {f : σ → V → F} (h : ∀ i ∈ s, Gr l L E (f i)) :
    Gr l L E fun t => ∑ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Gr.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem Gr.clm {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (T : F →L[ℝ] G) {f : V → F}
    (hf : Gr l L E f) : Gr l L E fun t => T (f t) := by
  refine ⟨hf.diff.mono fun t h => T.differentiableAt.comp t h, (T.isBigO_comp f l).trans hf.bdd, ?_⟩
  refine (((ContinuousLinearMap.compL ℝ V F G T).isBigO_comp (fderiv ℝ f) l).trans hf.der).congr' ?_
    EventuallyEq.rfl
  filter_upwards [hf.diff] with t h
  exact ((T.hasFDerivAt.comp t h.hasFDerivAt).fderiv).symm

theorem Gr.of_contDiffAt {t₀ : V} (hl : l ≤ 𝓝 t₀) (hL : (fun _ => (1 : ℝ)) =O[l] L) (hE : (fun _ => (1 : ℝ)) =O[l] E)
    {f : V → F} (hf : ContDiffAt ℝ 1 f t₀) : Gr l L E f :=
  ⟨((hf.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero).filter_mono hl,
    ((hf.continuousAt.isBigO_one ℝ).mono hl).trans hL,
    ((((hf.fderiv_right (m := 0) (by simp)).continuousAt).isBigO_one ℝ).mono hl).trans hE⟩

end Gen

theorem Gr.const (c : ℂ) : Gr l (fun _ => (1 : ℝ)) E (fun _ => c) :=
  ⟨Eventually.of_forall fun _ => differentiableAt_const _, isBigO_const_const _ one_ne_zero _, by
    rw [fderiv_fun_const]; exact isBigO_zero _ _⟩

theorem Gr.mul {f g : V → ℂ} (hf : Gr l (fun _ => (1 : ℝ)) E f)
    (hg : Gr l (fun _ => (1 : ℝ)) E g) : Gr l (fun _ => (1 : ℝ)) E fun t => f t * g t := by
  refine ⟨(hf.diff.and hg.diff).mono fun t h => h.1.fun_mul h.2, ?_, ?_⟩
  · simpa only [mul_one] using hf.bdd.mul hg.bdd
  have h1 : (fun t => f t • fderiv ℝ g t) =O[l] E := by simpa using hf.bdd.smul hg.der
  have h2 : (fun t => g t • fderiv ℝ f t) =O[l] E := by simpa using hg.bdd.smul hf.der
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hf.diff, hg.diff] with t h1 h2
  rw [fderiv_fun_mul h1 h2]

theorem Gr.prod {σ : Type} (s : Finset σ) {f : σ → V → ℂ} (h : ∀ i ∈ s, Gr l (fun _ => (1 : ℝ)) E (f i)) :
    Gr l (fun _ => (1 : ℝ)) E fun t => ∏ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Gr.const 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem Gr.det {n : ℕ} {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ p q, Gr l (fun _ => (1 : ℝ)) E fun t => M t p q) :
    Gr l (fun _ => (1 : ℝ)) E fun t => (M t).det := by
  simp only [det_apply']
  exact Gr.sum _ fun σ _ => (Gr.const _).mul (Gr.prod _ fun i _ => h _ _)

theorem Gr.sandwich {n : ℕ} {A B : V → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ p q, Gr l (fun _ => (1 : ℝ)) E fun t => A t p q)
    (hB : ∀ p q, Gr l (fun _ => (1 : ℝ)) E fun t => B t p q) (p q : Fin n) :
    Gr l (fun _ => (1 : ℝ)) E fun t => ((A t)ᴴ * B t * A t) p q := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Gr.sum _ fun k _ => (Gr.sum _ fun i _ =>
    (Gr.clm (Complex.conjCLE : ℂ →L[ℝ] ℂ) (hA i p)).mul (hB i k)).mul (hA k q)

theorem Gr.log {g R : V → ℝ} (hg : Gr l (fun _ => (1 : ℝ)) E g)
    (hR : ∀ᶠ t in l, Real.exp 1 ≤ R t) {c : ℝ} (hc : 0 < c) {m : ℕ} (hlo : ∀ᶠ t in l, c / R t ^ m ≤ g t) :
    Gr l (fun t => Real.log (R t)) (fun t => R t ^ m * E t) fun t => Real.log (g t) := by
  have hpos : ∀ᶠ t in l, 0 < R t ∧ 0 < g t := by
    filter_upwards [hR, hlo] with t h1 h2
    have := (Real.exp_pos 1).trans_le h1
    exact ⟨this, (by positivity : 0 < c / R t ^ m).trans_le h2⟩
  refine ⟨(hg.diff.and hpos).mono fun t h => h.1.log h.2.2.ne', ?_, ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hg.bdd.exists_pos
    refine IsBigO.of_bound (|Real.log c| + m + |Real.log C|) ?_
    filter_upwards [hC.bound, hR, hlo, hpos] with t h1 h2 h3 h4
    have hL : 1 ≤ Real.log (R t) := by
      rw [Real.le_log_iff_exp_le h4.1]; exact h2
    rw [norm_one, mul_one, Real.norm_of_nonneg h4.2.le] at h1
    have u := Real.log_le_log h4.2 h1
    have hRp := h4.1
    have d := Real.log_le_log (by positivity) h3
    rw [Real.log_div hc.ne' (pow_pos h4.1 m).ne', Real.log_pow] at d
    rw [Real.norm_of_nonneg (by linarith : 0 ≤ Real.log (R t)), Real.norm_eq_abs, abs_le]
    have a1 := le_mul_of_one_le_right (abs_nonneg (Real.log c)) hL
    have a2 := le_mul_of_one_le_right (abs_nonneg (Real.log C)) hL
    have a3 := neg_abs_le (Real.log c)
    have a4 := le_abs_self (Real.log C)
    have a5 := abs_nonneg (Real.log C)
    have a6 := abs_nonneg (Real.log c)
    have a7 : (0 : ℝ) ≤ m * Real.log (R t) := mul_nonneg (Nat.cast_nonneg m) (by linarith)
    constructor <;> nlinarith
  · have h1 : (fun t => (g t)⁻¹) =O[l] fun t => R t ^ m := by
      refine IsBigO.of_bound c⁻¹ ?_
      filter_upwards [hlo, hpos] with t h3 h4
      have hRp := h4.1
      rw [Real.norm_of_nonneg (inv_pos.2 h4.2).le, Real.norm_of_nonneg (pow_pos hRp m).le]
      refine (inv_anti₀ (by positivity) h3).trans_eq ?_
      rw [inv_div, div_eq_inv_mul]
    refine (h1.smul hg.der).congr' ?_ EventuallyEq.rfl
    filter_upwards [hg.diff, hpos] with t h h4
    rw [fderiv.log h h4.2.ne']

theorem det_lower {N k : ℕ} (hk : k ≤ N) {t₀ : V} (hl : l ≤ 𝓝 t₀) {R : V → ℝ} (hR : ∀ᶠ t in l, Real.exp 1 ≤ R t)
    {A : V → Matrix (Fin N) (Fin k) ℂ} (hA : ContinuousAt A t₀) (h0 : ((A t₀)ᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * A t₀).PosDef)
    {H : V → Matrix (Fin N) (Fin N) ℂ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hH : ∀ᶠ t in l, (H t).PosDef ∧ ((H t)⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
      (((C * R t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - (H t)⁻¹).PosSemidef) :
    ∃ c' > (0 : ℝ), ∀ᶠ t in l, c' / R t ^ N ≤ ((A t)ᴴ * H t * A t).det.re := by
  rw [Matrix.mul_one] at h0
  have hp := (Complex.pos_iff.1 h0.det_pos).1
  have hΦ : Continuous fun M : Matrix (Fin N) (Fin k) ℂ => (Mᴴ * M).det.re :=
    Complex.continuous_re.comp ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_det)
  have hev : ∀ᶠ t in 𝓝 t₀, ((A t₀)ᴴ * A t₀).det.re / 2 < ((A t)ᴴ * A t).det.re :=
    (hΦ.continuousAt.comp hA).eventually (lt_mem_nhds (half_lt_self hp))
  refine ⟨C⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2), by positivity, ?_⟩
  filter_upwards [hH, hR, hev.filter_mono hl] with t h1 h2 h3
  have hR1 : 1 ≤ R t := (Real.one_le_exp zero_le_one).trans h2
  have hR0 : 0 < R t := one_pos.trans_le hR1
  refine le_trans ?_ (GramDetSandwich.proof (H t) (A t) c (C * R t) hc h1.1 h1.2.1 h1.2.2).1
  calc C⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2) / R t ^ N
      ≤ C⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2) / R t ^ k :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hR1 hk)
    _ = (C * R t)⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2) := by
        rw [mul_inv, mul_pow, inv_pow (R t)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3.le (by positivity)

theorem quot_bounds {j N : ℕ} (hj : j ≤ N) (hN : 0 < N) {t₀ : V} (hl : l ≤ 𝓝 t₀) {R : V → ℝ}
    (hR : ∀ᶠ t in l, Real.exp 1 ≤ R t) (hE : (fun _ => (1 : ℝ)) =O[l] E)
    {S : V → Matrix (Fin N) (Fin N) ℂ} (hS : ∀ p q, ContDiffAt ℝ 1 (fun t => S t p q) t₀)
    (h0 : Function.Injective (S t₀).mulVec)
    {H : V → Matrix (Fin N) (Fin N) ℂ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hH : ∀ᶠ t in l, (H t).PosDef ∧ ((H t)⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
      (((C * R t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - (H t)⁻¹).PosSemidef)
    (hd : ∀ p q, ∀ᶠ t in l, DifferentiableAt ℝ (fun s => H s p q) t)
    (hD : ∀ p q, fderiv ℝ (fun s => H s p q) =O[l] E)
    (hG : ∀ᶠ t in l, ((S t)ᴴ * H t * S t).PosDef) :
    Gr l (fun t => Real.log (R t)) (fun t => R t ^ N * E t) (fun t =>
      (Real.log ((S t)ᴴ * H t * S t).det.re -
        Real.log (((S t)ᴴ * H t * S t).submatrix (headIdx hj) (headIdx hj)).det.re) / 2) ∧
    ∃ B : ℝ, ∀ᶠ t in l, quotNormSq hj ((S t)ᴴ * H t * S t) ≤ B := by
  have hSg : ∀ p q, Gr l (fun _ => (1 : ℝ)) E fun t => S t p q :=
    fun p q => Gr.of_contDiffAt hl (isBigO_refl _ _) hE (hS p q)
  have hHg : ∀ p q, Gr l (fun _ => (1 : ℝ)) E fun t => H t p q := fun p q =>
    ⟨hd p q, IsBigO.of_bound c⁻¹ (hH.mono fun t h => by
      rw [norm_one, mul_one]
      exact norm_entry_le h.1.posSemidef (GramDetSandwich.loewner_inv hN _ _ _ hc h.1 h.2.1 h.2.2).2.2 p q), hD p q⟩
  have hGg := Gr.sandwich hSg hHg
  have hSc : ContinuousAt S t₀ := continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => (hS p q).continuousAt
  have hPD : ((S t₀)ᴴ * 1 * S t₀).PosDef := Matrix.PosDef.one.conjTranspose_mul_mul_same h0
  obtain ⟨c1, hc1, h1⟩ := det_lower le_rfl hl hR hSc hPD hc hC hH
  obtain ⟨c2, hc2, h2⟩ := det_lower hj hl hR (A := fun t => (S t).submatrix id (headIdx hj))
    ((continuous_id.matrix_submatrix _ _).continuousAt.comp hSc)
    (by rw [← submatrix_gram']; exact hPD.submatrix (Fin.castLE_injective hj)) hc hC hH
  simp only [← submatrix_gram'] at h2
  have g1 := (Gr.clm Complex.reCLM (Gr.det hGg)).log hR hc1 h1
  have g2 := (Gr.clm Complex.reCLM (Gr.det (M := fun t => ((S t)ᴴ * H t * S t).submatrix (headIdx hj) (headIdx hj))
    fun p q => hGg _ _)).log hR hc2 h2
  refine ⟨?_, ?_⟩
  · have := (Gr.clm ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) g1).add
      (Gr.clm ((-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) g2)
    convert this using 2 with t
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply]
    ring
  · obtain ⟨B, hB⟩ := (Gr.det (M := fun t => ((S t)ᴴ * H t * S t).submatrix (tailIdx hj) (tailIdx hj))
      fun p q => hGg _ _).bdd.bound
    refine ⟨B, ?_⟩
    filter_upwards [hB, hG] with t h1 h2
    rw [norm_one, mul_one] at h1
    exact (quotNormSq_le hj h2).trans ((Complex.re_le_norm _).trans h1)

end LevelTowerAlt.MuBd
end
end
