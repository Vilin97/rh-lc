module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMixedSpaceNormSignCharacter

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormSign

open NumberField.InfinitePlace

variable {K : Type} [Field K] [NumberField K]

noncomputable def snorm (x : mixedSpace K) : ℝ :=
  (∏ w, x.1 w) * ∏ w, ‖x.2 w‖ ^ 2

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.snorm_mul {K : Type} [Field K] [NumberField K]
    (x y : NumberField.mixedEmbedding.mixedSpace K) :
    _root_.GlobalTheory.NormSign.snorm (x * y) = _root_.GlobalTheory.NormSign.snorm x * _root_.GlobalTheory.NormSign.snorm y := by
  simp only [_root_.GlobalTheory.NormSign.snorm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]
  ring

theorem snorm_smul (t : ℝ) (ht : 0 < t) (x : mixedSpace K) :
    ∃ c : ℝ, 0 < c ∧ snorm (t • x) = c * snorm x := by
  refine ⟨(∏ _w : {w : InfinitePlace K // IsReal w}, t) *
    ∏ _w : {w : InfinitePlace K // IsComplex w}, t ^ 2, by positivity, ?_⟩
  simp only [snorm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, _root_.norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow, Finset.prod_mul_distrib]
  ring

theorem continuous_snorm : Continuous (snorm : mixedSpace K → ℝ) := by
  unfold snorm
  fun_prop

theorem abs_snorm (x : mixedSpace K) : |snorm x| = mixedEmbedding.norm x := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, snorm, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (by positivity)]

theorem snorm_mixedEmbedding (x : K) :
    snorm (mixedEmbedding K x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x)
      (fun φ => φ x) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [Complex.ofReal_ratCast, h, ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x),
    prod_eq_prod_mul_prod, snorm, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod]
  have key : ∀ w : InfinitePlace K, (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w)
      = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    intro w
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
      star_involutive.eq_iff]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [key, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp w.2), Finset.pair_eq_singleton,
      Finset.prod_singleton, mixedEmbedding_apply_isReal, embedding_of_isReal_apply]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hne : w.1.embedding ≠ ComplexEmbedding.conjugate w.1.embedding := by
      rw [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
      exact not_isReal_iff_isComplex.mpr w.2
    rw [key, Finset.prod_pair hne, mixedEmbedding_apply_isComplex,
      ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

noncomputable def sgn (ε : ℂ) (t : ℝ) : ℂ := if 0 < t then 1 else if t < 0 then ε else 0

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.sgn_mul {ε : ℂ} (hε : ε * ε = 1) (a b : ℝ) :
    _root_.GlobalTheory.NormSign.sgn ε (a * b) = _root_.GlobalTheory.NormSign.sgn ε a * _root_.GlobalTheory.NormSign.sgn ε b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_pos_of_neg_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, hb.not_gt, hε]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_neg_of_neg_of_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, h.not_gt]
  · simp [_root_.GlobalTheory.NormSign.sgn]
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_neg_of_pos_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, hb.not_gt, h.not_gt]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h]

theorem norm_sgn {ε : ℂ} (hε : ε * ε = 1) {a : ℝ} (ha : a ≠ 0) : ‖sgn ε a‖ = 1 := by
  have h : ‖ε‖ = 1 := by
    rcases mul_self_eq_one_iff.mp hε with h | h <;> simp [h]
  rcases lt_or_gt_of_ne ha with h' | h'
  · simp [sgn, h', h'.not_gt, h]
  · simp [sgn, h']

theorem exists_normSign (K : Type) [Field K] [NumberField K] (ε : ℂ) (hε : ε * ε = 1) :
    ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧
      (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧
      ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧
      (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧
      ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  have hne : ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 → snorm x ≠ 0 := fun x hx => by
    rwa [← abs_snorm, abs_ne_zero] at hx
  refine ⟨fun x => sgn ε (snorm x), fun x y => ?_, fun t x ht => ?_, fun x hx => ?_,
    fun x hx => norm_sgn hε (hne x hx), fun β hβ => ?_⟩
  · simp only [snorm_mul, sgn_mul hε]
  · obtain ⟨c, hc, h⟩ := snorm_smul t ht x
    simp only [h, sgn_mul hε]
    simp [sgn, hc]
  · refine ContDiffAt.contDiffWithinAt ?_
    refine (contDiffAt_const (c := sgn ε (snorm x))).congr_of_eventuallyEq ?_
    rcases lt_or_gt_of_ne (hne x hx) with h | h
    · filter_upwards [continuous_snorm.continuousAt.eventually (gt_mem_nhds h)] with y hy
      simp [sgn, h, hy, h.not_gt, hy.not_gt]
    · filter_upwards [continuous_snorm.continuousAt.eventually (lt_mem_nhds h)] with y hy
      simp [sgn, h, hy]
  · have h0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    simp only [snorm_mixedEmbedding, ← Algebra.coe_norm_int, Rat.cast_intCast, sgn,
      Int.cast_pos, Int.cast_lt_zero]
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [h, h.not_gt]
    · simp [h]

end GlobalTheory.NormSign
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMixedSpaceNormSignCharacterStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem _root_.GlobalTheory.T.exists_mixedSpace_norm_sign_character : ∀ (K : Type) [Field K] [NumberField K] (ε : ℂ), ε * ε = 1 → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  first | exact @GlobalTheory.NormSign.exists_normSign | exact GlobalTheory.NormSign.exists_normSign | (intros; apply GlobalTheory.NormSign.exists_normSign <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousNormCharLFunctionNeZeroOne

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory
namespace NormCharL

theorem norm_cast_eq_one (K : Type) [Field K] [NumberField K] (m : ℕ) (β : 𝓞 K)
    (h : β - 1 ∈ Ideal.span {(m : 𝓞 K)}) : ((Algebra.norm ℤ β : ℤ) : ZMod m) = 1 := by
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 h
  have hβ : β = 1 + (m : 𝓞 K) * γ := by rw [mul_comm, hγ]; ring
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have key : (Int.castRingHom (ZMod m)).mapMatrix (Algebra.leftMulMatrix b β) = 1 := by
    rw [hβ, map_add (f := _), map_one, map_mul, map_natCast, map_add (f := _), map_one, map_mul, map_natCast]
    ext i j
    simp [Matrix.one_apply]
  have h2 := (Int.castRingHom (ZMod m)).map_det (Algebra.leftMulMatrix b β)
  rw [key, Matrix.det_one, ← Algebra.norm_eq_matrix_det] at h2
  simpa using h2

theorem sup_eq_top_iff (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : m.Prime)
    (I : Ideal (𝓞 K)) : I ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ ↔ ¬ m ∣ Ideal.absNorm I := by
  constructor
  · intro h hdvd
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hmem : i - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton']
      exact ⟨-z, by rw [← hiy]; ring⟩
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m i hmem
    have hd : Ideal.absNorm I ∣ (Algebra.norm ℤ i).natAbs := by
      rw [← Ideal.absNorm_span_singleton]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hi)
    have hz : ((Algebra.norm ℤ i : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 (hdvd.trans hd)
    rw [hz] at h1
    have : Fact m.Prime := ⟨hm⟩
    exact zero_ne_one h1
  · intro h
    have hc : Nat.Coprime (Ideal.absNorm I) m := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).2 h))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K) = (u : 𝓞 K) * (Ideal.absNorm I : 𝓞 K) + (v : 𝓞 K) * (m : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this
      exact this.symm
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem I)))
      (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem exists_continuous_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  intro K _ _ m hm χ cl hcl hχ
  have : Fact m.Prime := ⟨hm⟩
  set M : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)} with hMdef
  let ψ : ZMod m → ℂ := fun x => if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    by_cases hx : x = 0
    · simp [ψ, hx]
    by_cases hy : y = 0
    · simp [ψ, hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [ψ, dif_neg hx, dif_neg hy, dif_neg hxy]
    rw [← Units.val_mul, ← map_mul]
    congr 3
    ext
    simp
  have hψunit : ∀ u : (ZMod m)ˣ, ψ (u : ZMod m) = ((χ u : ℂˣ) : ℂ) := by
    intro u
    simp only [ψ, dif_neg u.ne_zero]
    congr 3
    ext
    simp
  let X : Ideal (𝓞 K) → ℂ := fun I => ψ (Ideal.absNorm I : ZMod m)
  have hcop : ∀ I : Ideal (𝓞 K), I ⊔ M = ⊤ ↔ (Ideal.absNorm I : ZMod m) ≠ 0 := by
    intro I
    rw [GlobalTheory.NormCharL.sup_eq_top_iff K m hm I, Ne, ZMod.natCast_eq_zero_iff]
  have hM0 : M ≠ ⊥ := by
    rw [hMdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hX0 : X ⊥ = 0 := by simp [X, hψ0]
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    simp only [X, map_mul, Nat.cast_mul, hψmul]
  have hXnorm : ∀ I, I ≠ ⊥ → I ⊔ M = ⊤ → ‖X I‖ = 1 := by
    intro I _ hI
    have hne := (hcop I).1 hI
    simp only [X, ψ, dif_neg hne]
    exact GlobalTheory.Mem.RayPrimes.norm_char χ _
  have hXzero : ∀ I, I ⊔ M ≠ ⊤ → X I = 0 := by
    intro I hI
    have : (Ideal.absNorm I : ZMod m) = 0 := by
      by_contra h
      exact hI ((hcop I).2 h)
    simp [X, this, hψ0]
  set ε : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hε
  have hεε : ε * ε = 1 := by
    rw [hε, ← Units.val_mul, ← map_mul]
    simp
  obtain ⟨φ, hφmul, hφhom, hφsm, hφnorm, hφβ⟩ := GlobalTheory.T.exists_mixedSpace_norm_sign_character K ε hεε
  have hXφ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ M → X (Ideal.span {β}) = φ (mixedEmbedding K β) := by
    intro β hβ0 hβ1
    rw [hφβ β hβ0]
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m β hβ1
    have hN0 : Algebra.norm ℤ β ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact hβ0
    simp only [X, Ideal.absNorm_span_singleton]
    split_ifs with hpos
    · have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = 1 := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le, h1]
      rw [this, ← Units.val_one, hψunit]
      simp
    · have hneg : Algebra.norm ℤ β ≤ 0 := le_of_not_gt hpos
      have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = ((-1 : (ZMod m)ˣ) : ZMod m) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg, Int.cast_neg, h1]
        simp
      rw [this, hψunit]
  obtain ⟨P, hPm, hPχ⟩ := hχ
  have hPtop : P.asIdeal ⊔ M = ⊤ := (GlobalTheory.NormCharL.sup_eq_top_iff K m hm P.asIdeal).2 hPm
  have hclX (Q : HeightOneSpectrum (𝓞 K)) (hQ : ¬ m ∣ Ideal.absNorm Q.asIdeal) :
      X Q.asIdeal = ((χ (cl Q) : ℂˣ) : ℂ) := by
    show ψ (Ideal.absNorm Q.asIdeal : ZMod m) = _
    rw [← hcl Q hQ, hψunit]
  have hnt : ∃ J, J ≠ ⊥ ∧ J ⊔ M = ⊤ ∧ X J ≠ 1 := by
    refine ⟨P.asIdeal, P.ne_bot, hPtop, ?_⟩
    rw [hclX P hPm]
    intro h
    exact hPχ (Units.val_eq_one.1 h)
  let c : HeightOneSpectrum (𝓞 K) → ℂ := fun Q => ((χ (cl Q) : ℂˣ) : ℂ)
  have hc : ∀ Q, ‖c Q‖ ≤ 1 := fun Q => (GlobalTheory.Mem.RayPrimes.norm_char χ (cl Q)).le
  have hcX : ∀ Q : HeightOneSpectrum (𝓞 K), ¬ M ≤ Q.asIdeal → c Q = X Q.asIdeal := by
    intro Q hQ
    have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
    have htop : Q.asIdeal ⊔ M = ⊤ := by
      refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left ?_)
      intro h
      exact hQ (h ▸ le_sup_right)
    rw [hclX Q ((GlobalTheory.NormCharL.sup_eq_top_iff K m hm Q.asIdeal).1 htop)]
  obtain ⟨L, hLd, hLe, hL1⟩ := GlobalTheory.idealCharacterL_continuation_ne_zero_one K M X φ hM0 hX0 hXmul
    hXnorm hXzero hφmul hφhom hφsm hφnorm hXφ hnt c hc hcX
  refine ⟨fun z => L ((max z.re 1 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · refine hLd.continuousOn.comp_continuous (by fun_prop) (fun z => ?_)
    show (0 : ℝ) < ((max z.re 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · simpa using hL1
  · intro s hs
    have hmax : max (s : ℂ).re 1 = s := by
      rw [Complex.ofReal_re]
      exact max_eq_left hs.le
    simp only [hmax]
    exact (hLe s (by rwa [Complex.ofReal_re])).symm

end NormCharL
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousNormCharLFunctionNeZeroOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem _root_.GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  first | exact @GlobalTheory.NormCharL.exists_continuous_ne_zero_one | exact GlobalTheory.NormCharL.exists_continuous_ne_zero_one | (intros; apply GlobalTheory.NormCharL.exists_continuous_ne_zero_one <;> assumption)
end
end
