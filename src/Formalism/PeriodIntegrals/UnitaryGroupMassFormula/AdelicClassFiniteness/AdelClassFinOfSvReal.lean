module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.BlkMulVecCat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.ExistsBoundedMultiplier
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Partial
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.DedekindDomain.Different
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorGramDet
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorBasis

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem successive_vector_basis : SvBasis := by
  intro E _ _ m M hfg hspan
  classical
  let M' : Submodule ℤ (Fin m → E) := M.restrictScalars ℤ
  have hfg' : M'.FG := hfg.restrictScalars
  have : Module.Finite ℤ M' := Module.Finite.iff_fg.2 hfg'
  have : Module.Free ℤ M' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ M'
  let e0 : Module.Free.ChooseBasisIndex ℤ M' → Fin m → E := fun i => (b i : Fin m → E)
  have hli : LinearIndependent ℤ e0 := b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ e0 := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hrep : ∀ x (hx : x ∈ M), x = ∑ i, (b.repr ⟨x, hx⟩ i) • e0 i := by
    intro x hx
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : M')).symm
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  have hmemM : ∀ x ∈ M, x ∈ Submodule.span ℚ (Set.range e0) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstab : ∀ c : E, ∀ v ∈ Submodule.span ℚ (Set.range e0), c • v ∈ Submodule.span ℚ (Set.range e0) := by
    intro c v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
      let α : 𝓞 E := ⟨y • c, hyi⟩
      have hαv : α • e0 i ∈ M := M.smul_mem α (b i).2
      have hyQ : (y : ℚ) ≠ 0 := Int.cast_ne_zero.2 hy0
      have : c • e0 i = ((y : ℚ)⁻¹) • (α • e0 i) := by
        have hα : (α • e0 i) = ((y : E) * c) • e0 i := by
          rw [Algebra.smul_def (A := E)] at *
          show ((y • c : E)) • e0 i = _
          rw [zsmul_eq_mul]
        rw [hα, mul_smul, ← smul_assoc]
        rw [show ((y : ℚ)⁻¹ • ((y : E))) = (1 : E) by
          rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel₀ (Int.cast_ne_zero.2 hy0)]]
        rw [one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (hmemM _ hαv)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have hspanQ : Submodule.span ℚ (Set.range e0) = ⊤ := by
    let W : Submodule E (Fin m → E) :=
      { toAddSubmonoid := (Submodule.span ℚ (Set.range e0)).toAddSubmonoid
        smul_mem' := fun c v hv => hstab c v hv }
    have hle : Submodule.span E (M : Set (Fin m → E)) ≤ W := Submodule.span_le.2 fun x hx => hmemM x hx
    rw [hspan] at hle
    rw [eq_top_iff]
    intro v _
    exact hle (Submodule.mem_top)
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M') ℚ (Fin m → E) :=
    Module.Basis.mk hliQ (by rw [hspanQ])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M') = m * Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi_fintype]
    simp
  let σ : Fin (m * Module.finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ M' := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e0 ∘ σ, hliQ.comp σ σ.injective, fun i => (b (σ i)).2, fun x hx => ?_⟩
  refine ⟨fun i => b.repr ⟨x, hx⟩ (σ i), ?_⟩
  conv_lhs => rw [hrep x hx]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  rfl

end PIW.AdelClassFin

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorCodifferent

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem successive_vector_codifferent : SvCodiff := by
  intro E _ _
  refine ⟨(NumberField.discr E).natAbs, Int.natAbs_pos.2 (NumberField.discr_ne_zero E), fun y hy => ?_⟩
  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hy a'
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E)
    (fun i => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
    (Submodule.mem_one.2 ⟨1, map_one _⟩) hmem
  rw [← NumberField.coe_discr] at hint
  have hx : IsIntegral ℤ (((NumberField.discr E : ℤ) : E) * y) := by
    convert hint using 1
    rw [Algebra.smul_def, mul_one, map_intCast]
  obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (NumberField.discr E).natAbs := ⟨_, rfl⟩
  rw [← hn]
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · rw [← hn] at h
    refine ⟨z, ?_⟩
    rw [hz, h, Int.cast_natCast]
  · rw [← hn] at h
    refine ⟨-z, ?_⟩
    rw [map_neg, hz, h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]

end PIW.AdelClassFin

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorMajorantE

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField Matrix
open scoped ComplexOrder

theorem svM_conj_form {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (d z : Fin n → ℂ) :
    star z ⬝ᵥ ((U * diagonal d * star U) *ᵥ z) =
      ∑ i, star ((star U *ᵥ z) i) * (d i * (star U *ᵥ z) i) := by
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have h : star z ᵥ* U = star (Uᴴ *ᵥ z) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]

theorem svM_term (r : ℝ) (w : ℂ) : star w * ((r : ℂ) * w) = ((r * ‖w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [mul_left_comm, Complex.conj_mul']

theorem successive_vector_majorant : SvMaj := by
  intro n J hJ hdet
  set U : Matrix (Fin n) (Fin n) ℂ := (hJ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  set ev := hJ.eigenvalues with hev
  have hspec : J = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U := by
    have h := hJ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hJ.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hJ.eigenvectorUnitary.2
  have hev0 : ∀ i, ev i ≠ 0 := by
    intro i h
    apply hdet
    rw [hJ.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h]; simp)
  refine ⟨U * diagonal (fun i => ((|ev i| : ℝ) : ℂ)) * star U, ?_, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|ev i| : ℝ) : ℂ))).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      exact Complex.zero_lt_real.2 (abs_pos.2 (hev0 i))
    have hinj : Function.Injective (star U).mulVec := by
      intro x y hxy
      have := congrArg (fun v => U *ᵥ v) hxy
      simpa [Matrix.mulVec_mulVec, hUU'] using this
    have h2 := hD.conjTranspose_mul_mul_same hinj
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← Matrix.star_eq_conjTranspose] at h2
  · have hdU : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, hUU', Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdU, one_mul, Matrix.det_diagonal,
      hJ.det_eq_prod_eigenvalues, norm_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    simp [hev]
  · intro z
    rw [hspec, svM_conj_form, svM_conj_form]
    simp only [svM_term]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, Complex.norm_real, Complex.ofReal_re,
      Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [abs_mul, abs_sq]

theorem successive_vector_majorant_e : SvMajE := by
  intro F E _ _ _ _ _ _ hCM m J hJ hdet
  have hstar : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := hCM.cmUnram.2.1
  have hTC : NumberField.IsTotallyComplex E := hCM.cmUnram.1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := by
    intro φ h
    have hc := hTC.isComplex (InfinitePlace.mk φ)
    rw [InfinitePlace.isComplex_mk_iff] at hc
    exact hc (ComplexEmbedding.isReal_iff.2 h)
  have hJe : ∀ i j, star (J j i) = J i j := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hherm : ∀ φ : E →+* ℂ, (J.map φ).IsHermitian := by
    intro φ
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [← hJe i j, hstar]
    rfl
  have hdetφ : ∀ φ : E →+* ℂ, (J.map φ).det ≠ 0 := by
    intro φ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).2 hdet
  have hmapT : ∀ M : Matrix (Fin m) (Fin m) ℂ, M.IsHermitian → M.map (starRingEnd ℂ) = Mᵀ := by
    intro M hM
    ext i j
    rw [Matrix.map_apply, Matrix.transpose_apply, ← hM.apply j i]
    rfl
  have hid : ∀ (N : Matrix (Fin m) (Fin m) ℂ) (z : Fin m → ℂ),
      star z ⬝ᵥ (N.map (starRingEnd ℂ) *ᵥ z) = starRingEnd ℂ (z ⬝ᵥ (N *ᵥ star z)) := by
    intro N z

    simp [dotProduct, mulVec, map_sum, map_mul]
  choose H0 hH0 using fun φ : E →+* ℂ => successive_vector_majorant m (J.map φ) (hherm φ) (hdetφ φ)
  let ι := Fintype.equivFin (E →+* ℂ)
  refine ⟨fun φ => if ι φ < ι (ComplexEmbedding.conjugate φ) then H0 φ
    else (H0 (ComplexEmbedding.conjugate φ)).map (starRingEnd ℂ), ?_⟩
  intro φ
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
  by_cases hp : ι φ < ι (ComplexEmbedding.conjugate φ)
  · have hp' : ¬ ι (ComplexEmbedding.conjugate φ) < ι φ := lt_asymm hp
    simp only [if_pos hp]
    refine ⟨(hH0 φ).1, (hH0 φ).2.1, (hH0 φ).2.2, ?_⟩
    rw [hcc, if_neg hp']
  · set ψ := ComplexEmbedding.conjugate φ with hψ
    have hψφ : ι ψ < ι (ComplexEmbedding.conjugate ψ) := by
      rw [hψ, hcc]
      refine lt_of_le_of_ne (not_lt.1 hp) fun h => hne φ (ι.injective h.symm ▸ rfl)
    have hJφ : J.map φ = (J.map ψ).map (starRingEnd ℂ) := by
      ext i j
      simp [hψ, ComplexEmbedding.conjugate_coe_eq]
    have hM := hH0 ψ
    simp only [if_neg hp, if_pos hψφ, ← hψ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmapT _ hM.1.1]
      exact hM.1.transpose
    · have hdc : ∀ N : Matrix (Fin m) (Fin m) ℂ,
          (N.map (starRingEnd ℂ)).det = starRingEnd ℂ N.det := fun N => by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [hmapT _ hM.1.1, Matrix.det_transpose, hM.2.1, hJφ, hdc, Complex.norm_conj]
    · intro z
      have h1 := hM.2.2 (star z)
      rw [star_star] at h1
      rw [hJφ, hid, hid, Complex.norm_conj, Complex.conj_re]
      exact h1
    · rw [Matrix.map_map]
      ext i j
      simp

end PIW.AdelClassFin
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.AdelClassFinOfSvReal

section

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

theorem adelClassFin_of_svReal (h : SvReal) : PI.AdelClassFin.AdelClassFin :=
  adelClassFin_of_open spOne existsBoundedMultiplier successive_vector_majorant_e successive_vector_codifferent successive_vector_basis successive_vector_gram_det h

end PIW.AdelClassFin

end
end
end
