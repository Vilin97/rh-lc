module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.GlRel
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.SubMat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.LineDeriv
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetHW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetRect
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.TopLie
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CommAll

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.commAll :
    ∀ (n : ℕ) (Ξ : Pre n) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), (∀ y, IsUnit y → Ξ.mat y * Z = Z * Ξ.mat y) →
      ∀ y, Ξ.mat y * Z = Z * Ξ.mat y := by
  intro n Ξ Z hZ y
  choose P hP using Ξ.poly
  let Q : Fin Ξ.d → Fin Ξ.d → MvPolynomial (Fin n × Fin n) ℂ := fun i j =>
    ∑ l, P i l * MvPolynomial.C (Z l j) - ∑ l, MvPolynomial.C (Z i l) * P l j
  have hent : ∀ (g : Matrix (Fin n) (Fin n) ℂ) i j,
      (Ξ.mat g * Z - Z * Ξ.mat g) i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) (Q i j) := by
    intro g i j

    simp [Q, Matrix.mul_apply, hP, map_sum, mul_comm]
  rw [← sub_eq_zero]
  ext i j
  rw [hent, Matrix.zero_apply]
  have hQ : Q i j = 0 := MvPolynomial.eq_of_eval_eq_on_gl (fun g => by
    rw [← hent, hZ (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit, sub_self, Matrix.zero_apply, map_zero])
  rw [hQ, map_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.PreSub

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.preSub :
    ∀ (n : ℕ) (Ξ : Pre n) (S : Submodule ℂ (Fin Ξ.d → ℂ)), (∀ y, ∀ v ∈ S, Ξ.mat y *ᵥ v ∈ S) →
      ∃ (Ξ' : Pre n) (A : Matrix (Fin Ξ.d) (Fin Ξ'.d) ℂ) (B : Matrix (Fin Ξ'.d) (Fin Ξ.d) ℂ),
        Ξ'.d = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ ∀ X, Ξ.D X * A = A * Ξ'.D X := by
  intro n Ξ S hS
  obtain ⟨d', A, B, ρ', hd, hBA, hA, hρ, hcomm⟩ :=
    UpperTheory.V.Weyl.subMat (Matrix (Fin n) (Fin n) ℂ) Ξ.d Ξ.mat S hS
  have hpoly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g,
      ρ' g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    choose p hp using Ξ.poly
    intro i j
    refine ⟨∑ l, (∑ k, MvPolynomial.C (B i k) * p k l) * MvPolynomial.C (A l j), fun g => ?_⟩
    rw [hρ]

    simp only [Matrix.mul_apply, map_sum, map_mul, MvPolynomial.eval_C, hp]
  let Ξ' : Pre n := ⟨d', ρ', hpoly⟩
  refine ⟨Ξ', A, B, hd, hBA, hA, fun X => ?_⟩
  have h0 : (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • X) 0 = 1 := by simp
  have hc : ∀ a b, HasDerivAt (fun t : ℂ => ((1 : Matrix (Fin n) (Fin n) ℂ) + t • X) a b) (X a b) 0 := by
    intro a b
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X a b)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
  have h1 := UpperTheory.V.Weyl.curve n Ξ _ X h0 hc
  have h2 := UpperTheory.V.Weyl.curve n Ξ' _ X h0 hc
  ext i j
  have e1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • X) * A) i j) ((Ξ.D X * A) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h1 i k).mul_const (A k j)
  have e2 : HasDerivAt (fun t : ℂ => (A * ρ' (1 + t • X)) i j) ((A * Ξ'.D X) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h2 k j).const_mul (A i k)
  simp only [hcomm] at e1
  exact e1.unique e2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetComm

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.qdetComm :
    ∀ (n : ℕ) (Ξ : Pre n) (u : ℂ) (y : Matrix (Fin n) (Fin n) ℂ), IsUnit y →
      Ξ.mat y * Formalism.REAL.qdet Ξ.E u = Formalism.REAL.qdet Ξ.E u * Ξ.mat y := by
  intro n Ξ u y hy
  obtain ⟨Q, hQ⟩ := hy.exists_left_inv
  have hW : ∀ a b : Fin n, y * Matrix.single a b (1 : ℂ) * Q =
      ∑ c, ∑ d, (y c a * Q b d) • Matrix.single c d (1 : ℂ) := by
    intro a b
    rw [Matrix.matrix_eq_sum_single (y * Matrix.single a b (1 : ℂ) * Q)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_single]
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  have h : ∀ a b : Fin n, Ξ.mat y * Ξ.E a b =
      (∑ c, ∑ d, (y c a * Q b d) • Ξ.E c d) * Ξ.mat y := by
    intro a b
    have h1 := UpperTheory.V.Weyl.adEq n Ξ y (Matrix.single a b 1) (y * Matrix.single a b (1 : ℂ) * Q)
      (by rw [mul_assoc, hQ, mul_one])
    rw [hW] at h1

    simp only [map_sum, map_smul] at h1
    exact h1
  rw [GlobalTheory.CapAdInv.qdet_semiconj _ _ _ h u,
    GlobalTheory.CapAdInv.qdet_ad _ (UpperTheory.V.Weyl.glRel n Ξ) y Q hQ u]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Scalar

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.scalar :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), v ≠ 0 → Ξ.IsTop ν v →
      ∃ Ξ' : Pre n, 0 < Ξ'.d ∧ Ξ'.d ≤ Ξ.d ∧ Ξ'.HasWt fun k => (ν k : ℂ) := by
  intro n Ξ ν v hv htop
  let S : Submodule ℂ (Fin Ξ.d → ℂ) :=
    Submodule.span ℂ (Set.range fun y : Matrix (Fin n) (Fin n) ℂ => Ξ.mat y *ᵥ v)
  have hS : ∀ y, ∀ w ∈ S, Ξ.mat y *ᵥ w ∈ S := by
    intro y w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [Matrix.mulVec_mulVec, ← map_mul]
      exact Submodule.subset_span ⟨y * z, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
      rw [Matrix.mulVec_add]
      exact S.add_mem hx hz
    | smul a x _ hx =>
      rw [Matrix.mulVec_smul]
      exact S.smul_mem a hx
  have hvS : v ∈ S := by
    have h : Ξ.mat 1 *ᵥ v ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using h
  obtain ⟨Ξ', A, B, hd, hBA, hA, hD⟩ := preSub n Ξ S hS
  obtain ⟨hdiag, hup⟩ := topLie n Ξ ν v htop
  refine ⟨Ξ', ?_, ?_, fun u => ?_⟩
  · rw [hd]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, hvS⟩, fun h => hv (congrArg Subtype.val h)⟩
  · rw [hd]
    simpa using Submodule.finrank_le S
  · set c : ℂ := ∏ k : Fin n, (u - ((k : ℕ) : ℂ) + (ν k : ℂ)) with hc
    have hQv : Formalism.REAL.qdet Ξ.E u *ᵥ v = c • v :=
      qdetHW n Ξ.d Ξ.E (fun k => (ν k : ℂ)) v (glRel n Ξ) hdiag hup u
    have hcomm : ∀ y, Ξ.mat y * Formalism.REAL.qdet Ξ.E u = Formalism.REAL.qdet Ξ.E u * Ξ.mat y :=
      commAll n Ξ _ (fun y hy => qdetComm n Ξ u y hy)
    have hQS : ∀ w ∈ S, Formalism.REAL.qdet Ξ.E u *ᵥ w = c • w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        rw [Matrix.mulVec_mulVec, ← hcomm y, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_smul]
      | zero => simp
      | add x z _ _ hx hz => rw [Matrix.mulVec_add, hx, hz, smul_add]
      | smul a x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]
    have hR := qdetRect n Ξ.d Ξ'.d Ξ.E Ξ'.E A (fun a b => hD _) u
    have hcA : Formalism.REAL.qdet Ξ.E u * A = c • A := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hQS _ (hA w), Matrix.smul_mulVec]
    show Formalism.REAL.qdet Ξ'.E u = c • 1
    calc Formalism.REAL.qdet Ξ'.E u = (B * A) * Formalism.REAL.qdet Ξ'.E u := by rw [hBA, Matrix.one_mul]
      _ = B * (Formalism.REAL.qdet Ξ.E u * A) := by rw [Matrix.mul_assoc, hR]
      _ = c • 1 := by rw [hcA, Matrix.mul_smul, hBA]
end
end
