module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.RingTheory.MvPolynomial.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrDeg

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrDeg :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), (rtr g f).totalDegree ≤ f.totalDegree := by
  intro n g f
  have hY : ∀ ij : Fin n × Fin n,
      (∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2) : MvPolynomial (Fin n × Fin n) ℂ).totalDegree ≤ 1 := by
    intro ij
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  conv_lhs => rw [MvPolynomial.as_sum f]

  simp only [rtr, map_sum, MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hY i)
    _ = s i := mul_one _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrMul

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrMul :
    ∀ (n : ℕ), (∀ f : Pol n, rtr 1 f = f) ∧ ∀ (g h : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), rtr (g * h) f = rtr g (rtr h f) := by
  intro n
  constructor
  · intro f
    have e : (rtr (1 : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n) = AlgHom.id ℂ (Pol n) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [rtr, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']
    rw [e]
    rfl
  · intro g h f
    have e : (rtr (g * h) : Pol n →ₐ[ℂ] Pol n) = (rtr g).comp (rtr h) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      rw [AlgHom.comp_apply]

      simp only [rtr, MvPolynomial.aeval_X, map_sum]
      have hx : ∀ x, (MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ k, MvPolynomial.X (ij.1, k) *
          MvPolynomial.C (g k ij.2)) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
          (MvPolynomial.X (i, x) * MvPolynomial.C (h x j)) =
          ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (g k x * h x j) := by
        intro x
        rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.sum_mul]
        simp only [mul_assoc, ← map_mul]

      simp only [hx, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrPoly

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrPoly :
    ∀ (n : ℕ) (f : Pol n) (φ : Pol n →ₗ[ℂ] ℂ), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      φ (rtr g f) = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
  intro n f
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro φ
    refine ⟨MvPolynomial.C (φ (MvPolynomial.C a)), fun g => ?_⟩
    have hc := (rtr g).commutes a
    rw [MvPolynomial.algebraMap_eq] at hc
    rw [hc, MvPolynomial.eval_C]
  | add p q hp hq =>
    intro φ
    obtain ⟨p1, h1⟩ := hp φ
    obtain ⟨p2, h2⟩ := hq φ
    exact ⟨p1 + p2, fun g => by rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _)]⟩
  | mul_X p ij hp =>
    intro φ
    choose P hP using fun k : Fin n =>
      hp (φ.comp (LinearMap.mulRight ℂ (MvPolynomial.X (ij.1, k) : Pol n)))
    refine ⟨∑ k, MvPolynomial.X (k, ij.2) * P k, fun g => ?_⟩
    have hX : rtr g (MvPolynomial.X ij : Pol n)
        = ∑ k, (MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2) := by
      simp [rtr, MvPolynomial.aeval_X]

    rw [map_mul, hX, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hP k g
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at hk
    rw [show rtr g p * ((MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2))
        = MvPolynomial.C (g k ij.2) * (rtr g p * MvPolynomial.X (ij.1, k)) by ring,
      MvPolynomial.C_mul', map_smul, smul_eq_mul, hk, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.PolPre

section

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.polPre :
    ∀ (n N : ℕ), ∃ (Ξ : Pre n) (e : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N ≃ₗ[ℂ] (Fin Ξ.d → ℂ)),
      ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N),
        (f' : Pol n) = rtr g f → Ξ.mat g *ᵥ e f = e f' := by
  intro n N
  let V := MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N
  have mem : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : V), rtr g (f : Pol n) ∈ V := by
    intro g f
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact (rtrDeg n g f).trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 f.2)
  let R : Matrix (Fin n) (Fin n) ℂ → V →ₗ[ℂ] V := fun g =>
    LinearMap.codRestrict V ((rtr g).toLinearMap.comp V.subtype) (mem g)
  have hR : ∀ g (f : V), ((R g f : V) : Pol n) = rtr g (f : Pol n) := fun g f => rfl
  let b := Module.finBasis ℂ V
  let M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun g => LinearMap.toMatrix b b (R g)
  have hR1 : R 1 = LinearMap.id := by
    ext f
    rw [hR, (rtrMul n).1]
    rfl
  have hRm : ∀ g h, R (g * h) = R g ∘ₗ R h := by
    intro g h
    ext f
    rw [hR, (rtrMul n).2]
    rfl
  let mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    { toFun := M
      map_one' := by
        show LinearMap.toMatrix b b (R 1) = 1
        rw [hR1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        show LinearMap.toMatrix b b (R (g * h)) = LinearMap.toMatrix b b (R g) * LinearMap.toMatrix b b (R h)
        rw [hRm]
        exact LinearMap.toMatrix_comp b b b (R g) (R h) }
  have poly : ∀ i j : Fin (Module.finrank ℂ V), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    intro i j
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
    obtain ⟨p, hp⟩ := rtrPoly n ((b j : V) : Pol n) φ
    refine ⟨p, fun g => ?_⟩
    rw [← hp]
    show LinearMap.toMatrix b b (R g) i j = _
    rw [LinearMap.toMatrix_apply, ← hR, ← b.coord_apply, ← hφ]
    rfl
  refine ⟨⟨Module.finrank ℂ V, mat, poly⟩, b.equivFun, ?_⟩
  intro g f f' hf
  show LinearMap.toMatrix b b (R g) *ᵥ b.repr f = b.repr f'
  rw [LinearMap.toMatrix_mulVec_repr]
  congr 2
  apply Subtype.ext
  rw [hR, hf]
end
end
