module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve

@[expose] public section

open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate

namespace GlobalTheory.QuadraticZeta

section Ring

variable {R : Type*} [CommRing R]

theorem eq_coord (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) (x : R) :
    x = (b.repr x 0 : R) + (b.repr x 1 : R) * b 1 := by
  conv_lhs => rw [← b.sum_repr x]
  simp [h0]

theorem repr_coord (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) (x y : ℤ) :
    b.repr (x + y * b 1) 0 = x ∧ b.repr (x + y * b 1) 1 = y := by
  have : (x + y * b 1 : R) = x • b 0 + y • b 1 := by simp [h0]
  rw [this]
  simp [-zsmul_eq_mul]

theorem discr_eq (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) {t n : ℤ}
    (hw : b 1 ^ 2 = t * b 1 - n) : Algebra.discr ℤ b = t ^ 2 - 4 * n := by
  have tr : ∀ x y : ℤ, Algebra.trace ℤ R (x + y * b 1) = 2 * x + y * t := by
    intro x y
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, h0, mul_one, (repr_coord b h0 x y).1,
      show (x + y * b 1 : R) * b 1 = (-(y * n) : ℤ) + (x + y * t : ℤ) * b 1 by
        push_cast; linear_combination (y : R) * hw, (repr_coord b h0 _ _).2]
    ring
  have t1 := tr 1 0
  have t2 := tr 0 1
  have t3 := tr (-n) t
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h0, mul_one, one_mul]
  rw [show b 1 * b 1 = (-n : ℤ) + t * b 1 by push_cast; linear_combination hw, t3]
  simp only [Int.cast_one, Int.cast_zero, zero_mul, add_zero, one_mul, zero_add] at t1 t2
  rw [t1, t2]
  ring

end Ring

theorem exists_basis {K : Type*} [Field K] [NumberField K] (h2 : finrank ℚ K = 2) :
    ∃ (b : Basis (Fin 2) ℤ (𝓞 K)) (t n : ℤ), b 0 = 1 ∧
      b 1 ^ 2 = t * b 1 - n ∧ discr K = t ^ 2 - 4 * n := by
  let e : Basis (Fin 2) ℤ (𝓞 K) := finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans h2)
  have h1 : (1 : 𝓞 K) = e.repr 1 0 • e 0 + e.repr 1 1 • e 1 := by
    conv_lhs => rw [← e.sum_repr 1]
    simp
  generalize e.repr 1 0 = x, e.repr 1 1 = y at h1
  have hc : IsCoprime x y := by
    refine isCoprime_of_dvd x y (fun h => by simp [h.1, h.2] at h1) ?_
    rintro z hz - ⟨x', rfl⟩ ⟨y', rfl⟩
    apply hz
    have hu : IsUnit (algebraMap ℤ (𝓞 K) z) :=
      IsUnit.of_mul_eq_one (x' • e 0 + y' • e 1) (by rw [h1]; simp; ring)
    have := hu.map (Algebra.norm ℤ)
    rw [Algebra.norm_algebraMap_of_basis e] at this
    exact (isUnit_pow_iff (by simp)).1 this
  obtain ⟨u, v, huv⟩ := hc
  have hd : IsUnit (e.det ![x • e 0 + y • e 1, -v • e 0 + u • e 1]) := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp only [Basis.toMatrix_apply]
    simp [-zsmul_eq_mul]
    convert isUnit_one using 1
    linarith
  obtain ⟨hi, hs⟩ := (e.is_basis_iff_det).2 hd
  let b : Basis (Fin 2) ℤ (𝓞 K) := Basis.mk hi hs.ge
  have h0 : b 0 = 1 := by simp [b, h1.symm, -zsmul_eq_mul]
  have hw : b 1 ^ 2 = (b.repr (b 1 ^ 2) 1 : ℤ) * b 1 - (-b.repr (b 1 ^ 2) 0 : ℤ) := by
    conv_lhs => rw [eq_coord b h0 (b 1 ^ 2)]
    push_cast
    ring
  exact ⟨b, _, _, h0, hw, by rw [← discr_eq_discr K b, discr_eq b h0 hw]⟩

variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

theorem exists_basis_embedding (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ) :
    ∃ (b : Basis (Fin 2) ℤ (𝓞 K)) (t : ℤ), b 0 = 1 ∧ 2 * (σ (b 1)).re = t ∧
      4 * (σ (b 1)).im ^ 2 = d := by
  obtain ⟨b, t, n, h0, hw, hD'⟩ := exists_basis h2
  have hd : (0 : ℝ) < d := by
    have := discr_ne_zero K
    exact_mod_cast (by omega : 0 < d)
  have e : (t : ℝ) ^ 2 - 4 * n = -d := by exact_mod_cast hD'.symm.trans hD
  have h : σ (b 1) ^ 2 = t * σ (b 1) - n := by
    have := congrArg (fun x : 𝓞 K => σ x) hw
    simpa using this
  refine ⟨b, t, h0, ?_⟩
  generalize σ (b 1) = W at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have h3 : W.im ≠ 0 := fun h => by
    rw [h] at h1
    nlinarith [sq_nonneg (2 * W.re - t)]
  have h4 : 2 * W.re = t := mul_right_cancel₀ h3 (by linarith)
  refine ⟨h4, ?_⟩
  rw [← h4] at h1 e
  nlinarith

theorem det_mul_im (σ : K →+* ℂ) (b : Basis (Fin 2) ℚ K) (h0 : b 0 = 1) (x y : K) :
    (b.det ![x, y] : ℝ) * (σ (b 1)).im = (σ y * conj (σ x)).im := by
  have hx : ∀ x : K, σ x = (b.repr x 0 : ℝ) + (b.repr x 1 : ℝ) * σ (b 1) := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    simp [h0, Rat.smul_def]
  rw [hx x, hx y, Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply]
  ring

section

variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD

theorem discr_pos : (0 : ℝ) < d := by
  have := discr_ne_zero K
  exact_mod_cast (by omega : 0 < d)

theorem norm_eq_sq (x : K) : (Algebra.norm ℚ x : ℝ) = ‖σ x‖ ^ 2 := by
  obtain ⟨b, t, h0, -, hi⟩ := exists_basis_embedding h2 hD σ
  have hd := discr_pos h2 hD
  have hi0 : (σ (b 1)).im ≠ 0 := fun h => by rw [h] at hi; linarith
  let b' : Basis (Fin 2) ℚ K := b.localizationLocalization ℚ ℤ⁰ K
  have e0 : b' 0 = 1 := by simp [b', h0]
  have e1 : b' 1 = b 1 := by simp [b']
  have := det_mul_im σ b' e0 (x * b' 0) (x * b' 1)
  rw [show b'.det ![x * b' 0, x * b' 1] = Algebra.norm ℚ x by
    rw [Algebra.norm_eq_matrix_det b', Basis.det_apply]
    congr 1
    ext i j
    fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul, Basis.toMatrix_apply], e0, e1] at this
  refine mul_right_cancel₀ hi0 (this.trans ?_)
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem absNorm_mul_sqrt (I : FractionalIdeal (𝓞 K)⁰ K)
    (bI : Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K)) :
    (absNorm I : ℝ) * (√d / 2) = |(σ (bI 1) * conj (σ (bI 0))).im| := by
  obtain ⟨b, t, h0, -, hi⟩ := exists_basis_embedding h2 hD σ
  let b' : Basis (Fin 2) ℚ K := b.localizationLocalization ℚ ℤ⁰ K
  have e0 : b' 0 = 1 := by simp [b', h0]
  have e1 : b' 1 = b 1 := by simp [b']
  rw [← det_mul_im σ b' e0, ← abs_det_basis_change b I bI, abs_mul, e1, ← hi,
    show 4 * (σ (b 1)).im ^ 2 = (2 * (σ (b 1)).im) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_mul,
    show Subtype.val ∘ bI = ![(bI 0 : K), bI 1] by ext i; fin_cases i <;> rfl]
  push_cast
  rw [abs_two]
  ring

include σ in
theorem unit_eq (hd : 4 < d) (u : (𝓞 K)ˣ) : u = 1 ∨ u = -1 := by
  obtain ⟨b, t, h0, hr, hi⟩ := exists_basis_embedding h2 hD σ
  have h1 : ‖σ (u : 𝓞 K)‖ ^ 2 = 1 := by
    have h := congrArg (Rat.cast : ℚ → ℝ) (NumberField.Units.norm K u)
    rw [Rat.cast_abs, norm_eq_sq h2 hD σ, abs_of_nonneg (by positivity)] at h
    simpa using h
  have h3 := eq_coord b h0 u
  generalize b.repr u 0 = x, b.repr u 1 = y at h3
  rw [h3, Complex.sq_norm, Complex.normSq_apply] at h1
  simp at h1
  have h4 : (2 * x + y * t) ^ 2 + y ^ 2 * d = 4 := by
    have : (2 * x + y * t : ℝ) ^ 2 + y ^ 2 * d = 4 := by
      rw [← hr, ← hi]
      linear_combination 4 * h1
    exact_mod_cast this
  have hy : y = 0 := by
    by_contra hy
    have : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * x + y * t)]
  subst hy
  have hx : x = 1 ∨ x = -1 := Int.isUnit_iff.1 (IsUnit.of_mul_eq_one x (by nlinarith))
  rcases hx with rfl | rfl
  · exact Or.inl (Units.ext (by simpa using h3))
  · exact Or.inr (Units.ext (by simpa using h3))

theorem hasSum_ideal (hd : 4 < d) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s S : ℝ} (hs : s ≠ 0)
    (h : HasSum (fun x : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =>
      (‖σ x‖ ^ 2 / absNorm 𝔞.1) ^ (-s)) S) :
    HasSum (fun I : Ideal (𝓞 K) => open Classical in
      if ((I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal
      then 2 * (Ideal.absNorm I : ℝ) ^ (-s) else 0) S := by
  have hΦ : ∀ x : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ I : Ideal (𝓞 K), (I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) = spanSingleton _ (x : K) := by
    intro x
    obtain ⟨I, hI⟩ := le_one_iff_exists_coeIdeal.1
      (show spanSingleton (𝓞 K)⁰ (x : K) * (𝔞⁻¹).1 ≤ 1 by
        rw [← 𝔞.mul_inv]
        gcongr
        exact spanSingleton_le_iff_mem.2 x.2)
    exact ⟨I, by rw [hI, mul_assoc, 𝔞.inv_mul, mul_one]⟩
  choose Φ hΦ using hΦ
  have hmem : ∀ x I, x ∈ Φ ⁻¹' {I} ↔
      (I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) = spanSingleton _ (x : K) := fun x I => by
    rw [← hΦ, Units.mul_left_inj, coeIdeal_inj, Set.mem_preimage, Set.mem_singleton_iff, eq_comm]
  have hN : (absNorm 𝔞.1 : ℝ) ≠ 0 := by simp [absNorm_eq_zero_iff]
  refine (h.tsum_fiberwise Φ).congr_fun fun I => ?_
  have hval : ∀ x : Φ ⁻¹' {I}, (‖σ x.1‖ ^ 2 / absNorm 𝔞.1) ^ (-s)
      = (Ideal.absNorm I : ℝ) ^ (-s) := fun x => by
    have := congrArg (fun J => ((absNorm J : ℚ) : ℝ)) ((hmem _ _).1 x.2)
    simp only [map_mul, coeIdeal_absNorm, absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs,
      Rat.cast_natCast, norm_eq_sq h2 hD σ, abs_pow, abs_norm] at this
    rw [← this, mul_div_cancel_right₀ _ hN]
  rw [tsum_congr hval, tsum_const, nsmul_eq_mul]
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp [Real.zero_rpow (neg_ne_zero.2 hs)]
  split_ifs with hP
  · obtain ⟨x, hx⟩ := (isPrincipal_iff _).1 hP
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp [hI] at hx
    have hxa : x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← spanSingleton_le_iff_mem, ← hx]
      exact (mul_le_mul_left coeIdeal_le_one _).trans (one_mul _).le
    have : Φ ⁻¹' {I} = {⟨x, hxa⟩, -⟨x, hxa⟩} := by
      ext y
      rw [hmem, hx, spanSingleton_eq_spanSingleton]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff, Submodule.coe_neg]
      constructor
      · rintro ⟨u, hu⟩
        rcases unit_eq h2 hD σ hd u with rfl | rfl
        · exact Or.inl (by simpa using hu.symm)
        · exact Or.inr (by simpa using hu.symm)
      · rintro (h | h)
        · exact ⟨1, by simp [h]⟩
        · exact ⟨-1, by simp [h]⟩
    rw [this, Nat.card_coe_set_eq, Set.ncard_pair]
    · simp
    · intro e
      exact hx0 (by simpa [Subtype.ext_iff, CharZero.eq_neg_self_iff] using e)
  · have : Φ ⁻¹' {I} = ∅ := Set.eq_empty_of_forall_notMem fun y hy =>
      hP ((isPrincipal_iff _).2 ⟨y, (hmem _ _).1 hy⟩)
    simp [this]


theorem exists_basis_of_image {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {ω : ℂ} {τ : ℍ} (hω : ω ≠ 0)
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) :
    ∃ b : Basis (Fin 2) ℤ (𝔞 : Submodule (𝓞 K) K), σ (b 0) = ω * τ ∧ σ (b 1) = ω := by
  obtain ⟨α, hα, eα⟩ := (h (ω * τ)).2 ⟨1, 0, by simp⟩
  obtain ⟨β, hβ, eβ⟩ := (h ω).2 ⟨0, 1, by simp⟩
  let v : Fin 2 → (𝔞 : Submodule (𝓞 K) K) := ![⟨α, hα⟩, ⟨β, hβ⟩]
  have hi : LinearIndependent ℤ v := by
    rw [LinearIndependent.pair_iff]
    intro m n e
    have e1 := congrArg (fun x : (𝔞 : Submodule (𝓞 K) K) => σ x) e
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, map_add (f := _), map_mul,
      map_intCast, eα, eβ, Submodule.coe_zero, map_zero] at e1
    have e2 : (m * τ + n : ℂ) = 0 := mul_left_cancel₀ hω (by linear_combination e1)
    have e3 : m = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
    exact ⟨e3, by simpa [e3] using e2⟩
  have hs : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨m, n, e⟩ := (h (σ x)).1 ⟨x, hx, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![m, n], Subtype.ext (σ.injective ?_)⟩
    simp [v, eα, eβ, ← e]
    ring
  exact ⟨Basis.mk hi hs, by simp [v, eα], by simp [v, eβ]⟩

omit h2 hD in
theorem ne_zero_of_image {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h0 : 𝔞 ≠ 0) {ω : ℂ} {τ : ℍ}
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) : ω ≠ 0 := by
  rintro rfl
  refine h0 (eq_zero_iff.2 fun x hx => σ.injective ?_)
  obtain ⟨m, n, e⟩ := (h (σ x)).1 ⟨x, hx, rfl⟩
  simp [← e]

theorem absNorm_eq_of_image {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {ω : ℂ} {τ : ℍ} (hω : ω ≠ 0)
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) :
    (absNorm 𝔞 : ℝ) = 2 * ‖ω‖ ^ 2 * τ.im / √d := by
  obtain ⟨b, e0, e1⟩ := exists_basis_of_image h2 hD σ hω h
  have := absNorm_mul_sqrt h2 hD σ 𝔞 b
  have hd := discr_pos h2 hD
  have hy := τ.im_pos
  rw [e0, e1, show (ω * conj (ω * τ)).im = -(‖ω‖ ^ 2 * τ.im) by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring, abs_neg,
    abs_of_nonneg (by positivity)] at this
  field_simp
  linarith

theorem hasSum_ideal_of_image (hd : 4 < d) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {ω : ℂ} {τ : ℍ}
    (h : ∀ z, z ∈ σ '' 𝔞.1 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) {s : ℝ} (hs : 1 < s)
    (hE : Summable fun p : {p : ℤ × ℤ // p ≠ 0} =>
      τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s)) :
    HasSum (fun I : Ideal (𝓞 K) => open Classical in
      if ((I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal
      then 2 * (Ideal.absNorm I : ℝ) ^ (-s) else 0)
      ((2 / √d) ^ s * ∑' p : {p : ℤ × ℤ // p ≠ 0},
        τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s)) := by
  have hω := ne_zero_of_image σ 𝔞.ne_zero h
  have hd0 := discr_pos h2 hD
  have hy := τ.im_pos
  obtain ⟨b, e0, e1⟩ := exists_basis_of_image h2 hD σ hω h
  refine hasSum_ideal h2 hD σ hd 𝔞 (by linarith) ?_
  rw [← ((finTwoArrowEquiv ℤ).symm.trans b.equivFun.symm.toEquiv).hasSum_iff,
    ← hasSum_subtype_iff_of_support_subset (s := {p : ℤ × ℤ | p ≠ 0})]
  · refine (hE.hasSum.mul_left _).congr_fun fun p => ?_
    have e : σ (b.equivFun.symm ![p.1.1, p.1.2]) = ω * (p.1.1 * τ + p.1.2) := by
      simp [e0, e1]
      ring
    change (‖σ (b.equivFun.symm ![p.1.1, p.1.2])‖ ^ 2 / _) ^ (-s) = _
    rw [e, absNorm_eq_of_image h2 hD σ hω h, Real.rpow_neg_eq_inv_rpow,
      show 2 * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul (norm_nonneg _),
      ← Real.div_rpow hy.le (by positivity), ← Real.mul_rpow (by positivity) (by positivity),
      norm_mul]
    congr 1
    have : ‖ω‖ ≠ 0 := by simpa using hω
    field_simp
  · intro p hp h0
    apply hp
    simp [h0, Real.zero_rpow (show -s ≠ 0 by linarith)]

theorem exists_periodPair (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L : PeriodPair, (L.lattice : Set ℂ) = σ '' 𝔞.1 := by
  let b : Basis (Fin 2) ℤ (𝔞.1 : Submodule (𝓞 K) K) := finBasisOfFinrankEq ℤ _
    ((fractionalIdeal_rank K 𝔞).trans ((RingOfIntegers.rank K).trans h2))
  have hd0 := discr_pos h2 hD
  have h0 : (σ (b 1) * conj (σ (b 0))).im ≠ 0 := by
    rw [← abs_ne_zero, ← absNorm_mul_sqrt h2 hD σ]
    have : (absNorm 𝔞.1 : ℝ) ≠ 0 := by simp [absNorm_eq_zero_iff]
    positivity
  refine ⟨⟨σ (b 0), σ (b 1), ?_⟩, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · ext z
    rw [SetLike.mem_coe, PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨b.repr ⟨x, hx⟩ 0, b.repr ⟨x, hx⟩ 1, ?_⟩
      have := congrArg (fun x : (𝔞.1 : Submodule (𝓞 K) K) => σ x) (b.sum_repr ⟨x, hx⟩)
      rw [Fin.sum_univ_two] at this
      simpa using this

end

end GlobalTheory.QuadraticZeta
