module

public import Formalism.PeriodIntegrals.FlagGramNonneg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.SumMulCommMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.BinaryFormMulEqNormSqAdd
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.ConjTMulMulApply

section

@[expose] public section

noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem tau_form {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (v w : V) :
    τ (hT v w) = star (fun n => τ (b.repr v n)) ⬝ᵥ
      (((PI.FlagGramNonneg.gram hT b).map τ) *ᵥ (fun n => τ (b.repr w n))) := by
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
  map_mul, starRingEnd_apply, hτ, dotProduct, mulVec, Matrix.map_apply, PI.FlagGramNonneg.gram,
  Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conjT_mul_mul_apply {m n : Type} [Fintype m] (A : Matrix m n ℂ) (B : Matrix m m ℂ) (i j : n) :
    (Aᴴ * B * A) i j = star (fun k => A k i) ⬝ᵥ (B *ᵥ fun k => A k j) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem gram_tau {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {ι : Type} (y : ι → V) (i j : ι) :
    ((Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((PI.FlagGramNonneg.gram hT b).map τ) *
      (Matrix.of fun n k => τ (b.repr (y k) n))) i j = τ (hT (y i) (y j)) := by
  rw [conjT_mul_mul_apply, tau_form hT b τ hτ]
  rfl

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.HasSignatureExistsNonneg

section

@[expose] public section

noncomputable section

open Matrix PI.FlagGramNonneg
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem cT_star_eq {m n : Type} (M : Matrix m n ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]

theorem form_mulVec {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (B : Matrix m m ℂ)
    (u : n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ (A *ᵥ u)) = star u ⬝ᵥ ((Aᴴ * B * A) *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem form_reindex {n m : Type} [Fintype n] [Fintype m] (e : n ≃ m) (J : Matrix n n ℂ)
    (x : n → ℂ) :
    star (fun i => x (e.symm i)) ⬝ᵥ ((J.reindex e e) *ᵥ (fun i => x (e.symm i))) =
      star x ⬝ᵥ (J *ᵥ x) := by
  have h : (J.reindex e e) *ᵥ (fun i => x (e.symm i)) = fun i => (J *ᵥ x) (e.symm i) := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    funext i
    simp [Function.comp_def]
  rw [h]
  simp only [dotProduct, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (x i) * (J *ᵥ x) i)

theorem Jpq_mulVec_of {p q : ℕ} (u : Fin p ⊕ Fin q → ℂ) (hu : ∀ j, u (Sum.inr j) = 0) :
    Jpq p q *ᵥ u = u := by
  have h0 : (u ∘ Sum.inr) = 0 := funext hu
  rw [Jpq, Matrix.fromBlocks_mulVec, h0]
  funext i
  cases i <;> simp [hu]

theorem hasSignature_exists_nonneg {N p q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Fin N) (Fin N) ℂ) (hJ : HasSignature J p q) (hq : q < Fintype.card ι)
    (X : Matrix (Fin N) ι ℂ) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ 0 ≤ (star (X *ᵥ c) ⬝ᵥ (J *ᵥ (X *ᵥ c))).re := by
  obtain ⟨e, P, hP⟩ := hJ
  let Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ)
  let Y : Matrix (Fin p ⊕ Fin q) ι ℂ := Q * X.submatrix e.symm id
  let K : Matrix (Fin q) ι ℂ := fun j l => Y (Sum.inr j) l
  have hk : LinearMap.ker (Matrix.mulVecLin K) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa [Module.finrank_fintype_fun_eq_card] using hq)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hk
  refine ⟨c, hc0, ?_⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
  have hy : ∀ j, (Y *ᵥ c) (Sum.inr j) = 0 := fun j => congrFun hc j
  have hx : (fun i => (X *ᵥ c) (e.symm i)) = (P : Matrix _ _ ℂ) *ᵥ (Y *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := Units.mul_inv P
    rw [hPQ, Matrix.one_mul]
    rfl
  have key : star (X *ᵥ c) ⬝ᵥ (J *ᵥ (X *ᵥ c)) = star (Y *ᵥ c) ⬝ᵥ (Y *ᵥ c) := by
    rw [cT_star_eq] at hP
    rw [← form_reindex e J (X *ᵥ c), hx, form_mulVec, hP, Jpq_mulVec_of _ hy]
  rw [key]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_self_nonneg ((Y *ᵥ c) i).re, mul_self_nonneg ((Y *ᵥ c) i).im]

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.NatAddZeroFinOne

section

@[expose] public section

noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem det_succ_schur {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det) :
    Z.det = (Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z (Fin.last r) (Fin.last r) - (fun b => Z (Fin.last r) (Fin.castSucc b)) ⬝ᵥ
        ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ (fun a => Z (Fin.castSucc a) (Fin.last r)))) := by
  haveI : Invertible (Z.submatrix Fin.castSucc Fin.castSucc) := Matrix.invertibleOfIsUnitDet _ h
  have hZ : Z.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks
      (Z.submatrix Fin.castSucc Fin.castSucc) (Matrix.of fun a (_ : Fin 1) => Z (Fin.castSucc a) (Fin.last r))
      (Matrix.of fun (_ : Fin 1) b => Z (Fin.last r) (Fin.castSucc b))
      (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => Z (Fin.last r) (Fin.last r)) := by
    ext (i | i) (j | j)
    · rfl
    · rw [Fin.fin_one_eq_zero j]
      rfl
    · rw [Fin.fin_one_eq_zero i]
      rfl
    · rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      rfl
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv Z, hZ, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Fin 1)]
  congr 1
  rw [Matrix.sub_apply, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] <;> rfl

theorem leadMinorE_succ {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE Z (r + 1) = Z.det := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  rfl

theorem leadMinorE_self {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dite_eq_left (Nat.le_succ r)]
  rfl

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.Gval

section

@[expose] public section

noncomputable section

open Matrix PI.FlagGramNonneg ComplexConjugate

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem main : PI.FlagGramNonneg := by
  unfold PI.FlagGramNonneg
  intro E _ _ _ V _ _ _ hT hS hN N b τ hτ p r T T' hsig hT0 hT'0 e e' z z' hf hf'
  obtain ⟨-, he, hez, hzz⟩ := hf
  obtain ⟨-, he', hez', hzz'⟩ := hf'
  have hsym : ∀ x y, hT y x = star (hT x y) := fun x y => by
    rw [← hS.eq x y, starRingEnd_apply]
  set Z := zhat hT (fvec e z) (fvec e' z') with hZ
  have hsub : Z.submatrix Fin.castSucc Fin.castSucc = amat hT e e' := by
    ext a c
    simp [hZ, zhat, fvec, amat]
  have hg : gval Z (T : E) (T' : E) = Z.det * star Z.det -
      (T : E) * T' * ((amat hT e e').det * star (amat hT e e').det) := by
    rw [gval, leadMinorE_succ, leadMinorE_self, hsub]
  by_cases hA : IsUnit (amat hT e e').det
  ·
    have hsubU : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [hsub]; exact hA
    have hrow : (fun c => Z (Fin.last r) (Fin.castSucc c)) = vvec hT z e' := by
      funext c; simp [hZ, zhat, fvec, vvec]
    have hcol : (fun a => Z (Fin.castSucc a) (Fin.last r)) = uvec hT e z' := by
      funext a; simp [hZ, zhat, fvec, uvec]
    have hll : Z (Fin.last r) (Fin.last r) = hT z z' := by
      simp [hZ, zhat, fvec]
    have hdet : Z.det = (amat hT e e').det * sval hT e e' z z' := by
      rw [det_succ_schur Z hsubU, hsub, hll, hrow, hcol]
      rfl

    have hs : (T : ℝ) * T' ≤ Complex.normSq (τ (sval hT e e' z z')) := by
      by_contra hlt
      push_neg at hlt
      set y : Fin r ⊕ Fin 2 → V :=
        Sum.elim (yv hT e e') ![zt hT e e' z, zt' hT e e' z'] with hy
      have hyz : ∀ a, hT (zt hT e e' z) (yv hT e e' a) = 0 := fun a => by
        rw [hsym, yv_zt (hS := hS) (hA := hA) (he := he) (hez := hez) (a := a), star_zero]
      have hyz' : ∀ a, hT (zt' hT e e' z') (yv hT e e' a) = 0 := fun a => by
        rw [hsym, yv_zt' (hA := hA) (he' := he') (hez' := hez') (a := a), star_zero]
      have hz'z : hT (zt' hT e e' z') (zt hT e e' z) = star (sval hT e e' z z') := by
        rw [hsym, zt_zt' (hA := hA)]
      have hG : (Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((gram hT b).map τ) *
          (Matrix.of fun n k => τ (b.repr (y k) n)) =
          gamma r T T' (τ (sval hT e e' z z')) := by
        ext i j
        rw [gram_tau hT b τ hτ y i j]
        rcases i with a | i <;> rcases j with c | j
        · by_cases hac : a = c
          · subst hac
            simp [hy, gamma, yv_yv (hS := hS) (hA := hA) (he := he) (he' := he'), map_ofNat]
          · simp [hy, gamma, yv_yv (hS := hS) (hA := hA) (he := he) (he' := he'), hac]
        · fin_cases j <;> simp [hy, gamma, yv_zt (hS := hS) (hA := hA) (he := he) (hez := hez), yv_zt' (hA := hA) (he' := he') (hez' := hez')]
        · fin_cases i <;> simp [hy, gamma, hyz, hyz']
        · fin_cases i <;> fin_cases j <;>
            simp [hy, gamma, zt_zt (hS := hS) (he := he) (hez := hez), zt'_zt' (hS := hS) (he' := he') (hez' := hez'), zt_zt' (hA := hA), hz'z, hzz, hzz', hτ]
      have hcard : r + 1 < Fintype.card (Fin r ⊕ Fin 2) := by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; omega
      obtain ⟨c, hc0, hcnn⟩ := hasSignature_exists_nonneg _ hsig hcard
        (Matrix.of fun n k => τ (b.repr (y k) n))
      rw [form_mulVec, hG] at hcnn
      have hneg := gamma_neg r T T' (by exact_mod_cast hT0) (by exact_mod_cast hT'0) _ hlt c hc0
      linarith
    refine ⟨Complex.normSq (τ (amat hT e e').det) *
      (Complex.normSq (τ (sval hT e e' z z')) - T * T'),
      mul_nonneg (Complex.normSq_nonneg _) (by linarith), ?_⟩
    rw [hg, hdet]
    simp only [map_sub, map_mul, star_mul', hτ, map_natCast]
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    ring
  ·
    have h0 : (amat hT e e').det = 0 := by
      by_contra h
      exact hA (isUnit_iff_ne_zero.mpr h)
    refine ⟨Complex.normSq (τ Z.det), Complex.normSq_nonneg _, ?_⟩
    rw [hg, h0]
    simp [hτ, Complex.mul_conj]

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagGramNonneg

section

@[expose] public section

theorem flag_gram_nonneg : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
end
end
