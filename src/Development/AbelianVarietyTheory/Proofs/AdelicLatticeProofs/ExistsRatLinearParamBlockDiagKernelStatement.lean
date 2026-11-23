module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRationalStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatProjectorOfAutStableMatrices

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatProj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def entryEquiv (ι : Type) : Matrix ι ι ℂ ≃ₗ[ℂ] (ι × ι → ℂ) where
  toFun X := fun kl => X kl.1 kl.2
  invFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_entry (w : Matrix ι ι ℂ) (k : ι × ι) :
    (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = w k.1 k.2 := by
  rw [Module.Basis.ofEquivFun_repr_apply]; rfl

noncomputable def castLin (ι : Type) : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℂ where
  toFun X := X.map (algebraMap ℚ ℂ)
  map_add' X Y := by ext i j; simp
  map_smul' q X := by ext i j; simp [Rat.smul_def]

noncomputable def linExtLin (c : ι × ι → ι × ι → ℚ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X := linExt c X
  map_add' X Y := by ext i j; simp [linExt, mul_add, Finset.sum_add_distrib]
  map_smul' a X := by ext i j; simp [linExt, Finset.mul_sum, mul_left_comm]

theorem linExt_eq_sum (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (X : Matrix ι ι ℂ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) X =
      ∑ kl : ι × ι, X kl.1 kl.2 • castLin ι (p (single kl.1 kl.2 1)) := by
  ext i j
  simp [linExt, castLin, Matrix.sum_apply, mul_comm]

theorem linExt_cast (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (Y : Matrix ι ι ℚ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (castLin ι Y) = castLin ι (p Y) := by
  rw [linExt_eq_sum]
  have hY : Y = ∑ kl : ι × ι, Y kl.1 kl.2 • single kl.1 kl.2 (1 : ℚ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [Fintype.sum_prod_type]
    simp [Matrix.smul_single]
  conv_rhs => rw [hY]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [map_smul, map_smul]
  ext i j
  simp [castLin, Rat.smul_def]

theorem exists_rat_projector : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  intro ι _ _ E hE
  let E₀ : Submodule ℚ (Matrix ι ι ℚ) := (E.restrictScalars ℚ).comap (castLin ι)
  obtain ⟨π, hπ⟩ : ∃ π : Matrix ι ι ℚ →ₗ[ℚ] E₀, ∀ x : E₀, π x = x := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective E₀.subtype E₀.ker_subtype
    exact ⟨g, fun x => LinearMap.congr_fun hg x⟩
  let p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ := E₀.subtype ∘ₗ π
  refine ⟨fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2, fun X => ?_, fun x hx => ?_⟩
  · rw [linExt_eq_sum]
    exact E.sum_mem fun kl _ => E.smul_mem _ (π (single kl.1 kl.2 1)).2
  · have hd := GlobalTheory.T.galoisStable_submodule_le_span_rational (Matrix ι ι ℂ) (ι × ι) (Module.Basis.ofEquivFun (entryEquiv ι)) E
      (fun σ w hw => ⟨w.map σ, hE σ w hw, fun k => by
        rw [repr_entry, repr_entry]; rfl⟩) hx
    have key : Set.EqOn (linExtLin fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (LinearMap.id (R := ℂ))
        {w | w ∈ E ∧ ∀ k, ∃ q : ℚ, (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = q} := by
      rintro w ⟨hw, hq⟩
      choose q hq using hq
      have hwq : w = castLin ι (Matrix.of fun i j => q (i, j)) := by
        ext i j
        have := hq (i, j)
        rw [repr_entry] at this
        simpa [castLin] using this
      have hmem : (Matrix.of fun i j => q (i, j)) ∈ E₀ := by
        change castLin ι _ ∈ E
        rw [← hwq]; exact hw
      have h1 : p (Matrix.of fun i j => q (i, j)) = Matrix.of fun i j => q (i, j) :=
        congrArg Subtype.val (hπ ⟨_, hmem⟩)
      have h2 := linExt_cast p (Matrix.of fun i j => q (i, j))
      rw [h1, ← hwq] at h2
      exact h2
    exact LinearMap.eqOn_span key hd

end GlobalTheory.ClassFin.RatProj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatProjectorOfAutStableMatricesStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_projector_of_autStable_matrices : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  first | exact @GlobalTheory.ClassFin.RatProj.exists_rat_projector | exact GlobalTheory.ClassFin.RatProj.exists_rat_projector | (intros; apply GlobalTheory.ClassFin.RatProj.exists_rat_projector <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneAddSmulMemOfSqZero

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_poly_ev_line {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial (ι × ι) ℚ)
    (A B : Matrix ι ι ℂ) : ∃ p : Polynomial ℂ, ∀ t : ℂ, p.eval t = ev f (A + t • B) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨Polynomial.C (algebraMap ℚ ℂ a), fun t => by simp [ev]⟩
  | add f g hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    refine ⟨p + q, fun t => ?_⟩
    rw [Polynomial.eval_add, hp, hq]
    simp [ev]
  | mul_X f ij hf =>
    obtain ⟨p, hp⟩ := hf
    refine ⟨p * (Polynomial.C (A ij.1 ij.2) + Polynomial.X * Polynomial.C (B ij.1 ij.2)), fun t => ?_⟩
    rw [Polynomial.eval_mul, hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    simp [ev]

theorem one_add_smul_mem_of_sq_zero :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ →
      ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  intro ι _ _ Γ hΓ ε hε h1 t
  have hn : ∀ n : ℕ, 1 + (n : ℂ) • ε ∈ Γ := by
    intro n
    induction n with
    | zero => simpa using hΓ.one_mem
    | succ n ih =>
      have h := hΓ.mul_mem _ ih _ h1
      have e : (1 + (n : ℂ) • ε) * (1 + ε) = 1 + ((n + 1 : ℕ) : ℂ) • ε := by
        rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hε, smul_zero, add_zero, Nat.cast_succ,
          add_smul, one_smul, add_assoc]
      rwa [e] at h
  apply hΓ.closed
  intro f hf
  obtain ⟨p, hp⟩ := exists_poly_ev_line f 1 ε
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective ?_
    intro n
    show p.eval (n : ℂ) = 0
    rw [hp]
    exact hf _ (hn n)
  rw [← hp, hp0, Polynomial.eval_zero]

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneAddSmulMemOfSqZeroStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.one_add_smul_mem_of_sq_zero' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  first | exact @GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero | exact GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero | (intros; apply GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatLinearParamBlockDiagKernel

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem corner_mul_corner {A : Type} [Ring A] (E x y : A) (hE : E * E = E)
    (hx : E * x * (1 - E) = x) (hy : E * y * (1 - E) = y) : x * y = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc x * y = (E * x * (1 - E)) * (E * y * (1 - E)) := by rw [hx, hy]
    _ = E * x * ((1 - E) * E) * y * (1 - E) := by simp only [mul_assoc]
    _ = 0 := by rw [h]; simp

theorem exists_linExt_corner_proj : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ ∀ ε : Matrix ι ι ℂ, 1 + ε ∈ Γ → e.map (algebraMap ℚ ℂ) * ε * (1 - e.map (algebraMap ℚ ℂ)) = ε → linExt c ε = ε := by
  intro ι _ _ Γ e hΓ he
  set E : Matrix ι ι ℂ := e.map (algebraMap ℚ ℂ) with hEdef
  have hE : E * E = E := by
    rw [hEdef, ← Matrix.map_mul, he]
  let S : Submodule ℂ (Matrix ι ι ℂ) :=
    { carrier := {ε | 1 + ε ∈ Γ ∧ E * ε * (1 - E) = ε}
      zero_mem' := ⟨by simpa using hΓ.one_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨?_, by rw [mul_add, add_mul, hx2, hy2]⟩
        have h0 := corner_mul_corner E x y hE hx2 hy2
        have h1 := hΓ.mul_mem _ hx1 _ hy1
        have h2 : (1 + x) * (1 + y) = 1 + (x + y) := by
          rw [mul_add, add_mul, add_mul, h0]; simp [add_assoc]
        rwa [h2] at h1
      smul_mem' := by
        rintro t x ⟨hx1, hx2⟩
        refine ⟨GlobalTheory.T.one_add_smul_mem_of_sq_zero' ι Γ hΓ x (corner_mul_corner E x x hE hx2 hx2) hx1 t, ?_⟩
        rw [Matrix.mul_smul, Matrix.smul_mul, hx2] }
  have hS : ∀ σ : ℂ ≃+* ℂ, ∀ x ∈ S, x.map σ ∈ S := by
    rintro σ x ⟨hx1, hx2⟩
    have hEσ : (σ : ℂ →+* ℂ).mapMatrix E = E := by
      ext i j
      simp [hEdef]
    have hx : x.map σ = (σ : ℂ →+* ℂ).mapMatrix x := rfl
    refine ⟨?_, ?_⟩
    · have h1 := hΓ.aut_mem σ _ hx1
      have h2 : (1 + x).map σ = (σ : ℂ →+* ℂ).mapMatrix (1 + x) := rfl
      rw [h2, map_add (f := _), map_one] at h1
      exact h1
    · have h3 := congrArg (σ : ℂ →+* ℂ).mapMatrix hx2
      rw [map_mul, map_mul, map_sub, map_one, hEσ] at h3
      exact h3
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_rat_projector_of_autStable_matrices ι S hS
  exact ⟨c, fun X => hc1 X, fun ε h1 h2 => hc2 ε ⟨h1, h2⟩⟩

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatLinearParamBlockDiagKernelStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_linear_param_blockDiag_kernel : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ ∀ ε : Matrix ι ι ℂ, 1 + ε ∈ Γ → e.map (algebraMap ℚ ℂ) * ε * (1 - e.map (algebraMap ℚ ℂ)) = ε → linExt c ε = ε := by
  first | exact @GlobalTheory.ClassFin.exists_linExt_corner_proj | exact GlobalTheory.ClassFin.exists_linExt_corner_proj | (intros; apply GlobalTheory.ClassFin.exists_linExt_corner_proj <;> assumption)
end
end
