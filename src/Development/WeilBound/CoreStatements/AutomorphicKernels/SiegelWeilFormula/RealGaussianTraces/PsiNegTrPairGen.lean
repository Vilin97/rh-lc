module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCN

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tri

variable {R : Type} [CommRing R] {ρ : ℕ}

def UTri (T : Matrix (Fin ρ) (Fin ρ) R) : Prop := ∀ j i, i ≤ j → (T - 1) j i = 0

theorem left_inv {K : Type} [Field K] {n : ℕ} (C : Matrix (Fin n) (Fin ρ) K) (h : LinearIndependent K C.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) K, L * C = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' C, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end Tri

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def eA : Matrix (Fin B.rank) (Fin d.ρ) (AE D) := d.e.map (incA D)

def lA : Matrix (Fin d.ρ) (Fin B.rank) (AE D) := (left_inv d.e d.e_iso.1).choose.map (incA D)

def tM (n : GA D B) : Matrix (Fin d.ρ) (Fin d.ρ) (AE D) := HMul.hMul (lA d) (HMul.hMul (mt B n) (eA d))

def bV (n : GA D B) (x : Fin B.rank → D.host.E) : Fin d.ρ → AE D := (lA d).mulVec ((mt B n).mulVec (ratV x) - ratV x)

def Perp (x : Fin B.rank → D.host.E) : Prop :=
  (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram).mulVec x = 0

def Good (n : GA D B) : Prop :=
  HMul.hMul (mt B n) (eA d) = HMul.hMul (eA d) (tM d n) ∧ UTri (tM d n) ∧
    ∀ x, Perp d x → (mt B n).mulVec (ratV x) = ratV x + (eA d).mulVec (bV d n x)

variable {d}


theorem trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R] (r : E) :
    Algebra.trace R (R ⊗[F] E) (inclR R r) = algebraMap F R (Algebra.trace F E r) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]
  rfl

end Formalism.L2.Fam.ThC

end
end
end

-- Source module: Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCJ

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem alg_trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), add_add_add_comm]
  | tmul a e =>
    have h4 : (a ⊗ₜ[F] e : R ⊗[F] E) = a • inclR R e := by
      show _ = a • ((1 : R) ⊗ₜ[F] e)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h5 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h5, ← TensorProduct.tmul_add, ← h, h4, map_smul, trace_gen, smul_eq_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]

end Gen

variable {D : D7}

variable {V W : HSp D}


end Formalism.L2.Fam.ThC

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.TraceAdd

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (y : E) : σ (σ y) = y := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2, hCM.2.2.2, star_star]

theorem sig_nt (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra h
  push Not at h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc := hCM.2.1.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  apply hc
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq]
  have := hCM.2.2.2 τ x
  rw [h x] at this
  exact this.symm

theorem trace_add (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (z : Ainf F ⊗[F] E) :
    algebraMap (Ainf F) (Ainf F ⊗[F] E) (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) = z + sigR (Ainf F) σ z := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
  exact Formalism.L2.Fam.ThC.alg_trace_gen σ
    (PI.OmLocU.SdB.trace_eq_add σ (sig_sig σ hCM) (sig_nt σ hCM) hCM.2.2.1) z

end PositivityTheory.SiegelWeilFormula.GReal
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.PsiNegTrPairGen

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem th_half (θ : Ainf F ⊗[F] E →+* ℂ) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
  rw [← IsScalarTower.algebraMap_apply]
  have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  exact this

theorem th_trPair (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (trPair (Ainf F) S G)) = (((S.map θ * G.map θ).trace.re : ℝ) : ℂ) := by
  rw [trPair, map_mul, map_mul, th_half, trace_add σ hCM, map_add (f := _), hc]
  have e : θ (∑ a, ∑ c, S a c * G c a) = (S.map θ * G.map θ).trace := by

    simp [Matrix.trace, Matrix.mul_apply, map_sum, map_mul]
  rw [e, Complex.star_def, Complex.add_conj]
  push_cast
  ring

theorem tmul_one_eq (x : Ainf F) : (x ⊗ₜ[F] (1 : E)) = algebraMap (Ainf F) (Ainf F ⊗[F] E) x := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem psi_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ)) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, th_trPair σ hCM (θ i) (hP.conj i)]

theorem psi_neg_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (-trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (-(((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ))) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, map_neg, map_neg, th_trPair σ hCM (θ i) (hP.conj i)]

theorem map_isHerm (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (b : HermR (Ainf F) σ n) :
    ((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map θ).IsHermitian := by
  ext a c
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← hc]
  exact congrArg θ (b.2 a c)

theorem gramX_eq {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) :
    gramX ε x = xᴴ * Matrix.diagonal (sgn ε) * x := by
  ext i j

  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, Matrix.mul_apply,
  Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
  if_true, sgn]
  simp only [Finset.sum_filter, if_true, Bool.false_eq_true, if_false]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

theorem gramX_isHerm {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) : (gramX ε x).IsHermitian := by
  rw [gramX_eq, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  have hs : star (sgn ε) = sgn ε := by
    funext a
    simp only [Pi.star_apply, sgn]
    split_ifs <;> simp
  rw [hs]

end PositivityTheory.SiegelWeilFormula.GReal
end
end
end
