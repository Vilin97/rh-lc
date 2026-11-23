module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonalStatement
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PiTensorProduct
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOne

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusAngles

theorem exp_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw] at h
  simpa [mul_comm] using h

theorem exp_neg_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (-(Complex.I * (Complex.arg w : ℂ))) = w⁻¹ := by
  rw [Complex.exp_neg, exp_I_arg hw]

theorem exists_angles_of_prod_eq_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 →
    ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  intro r z hz hp
  rcases r with _ | n
  · exact ⟨fun _ => 0, fun a => a.elim0⟩
  · refine ⟨fun k => Complex.arg (z ⟨k, by omega⟩), fun a => ?_⟩
    unfold angles
    split_ifs with h
    · exact exp_I_arg (hz _)
    · have ha : a = Fin.last n := by ext; simp at h ⊢; omega
      subst ha
      rw [Fin.prod_univ_castSucc] at hp
      have hlast : z (Fin.last n) = (∏ k : Fin n, z k.castSucc)⁻¹ := by
        exact eq_inv_of_mul_eq_one_right hp
      rw [hlast, Complex.ofReal_neg, Complex.ofReal_sum, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
        Complex.exp_sum, ← Finset.prod_inv_distrib]
      show ∏ k : Fin n, Complex.exp (-(Complex.I * (Complex.arg (z ⟨k, _⟩) : ℂ))) = _
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [exp_neg_I_arg (hz _)]
      rfl

end GlobalTheory.TorusAngles
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOneStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 → ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  first | exact @GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | exact GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | (intros; apply GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZero

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

theorem hasStrictFDerivAt_torus_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  refine hasStrictFDerivAt_pi'' fun τ => hasStrictFDerivAt_pi'' fun a => hasStrictFDerivAt_pi'' fun b => ?_
  set A : Fin r → ((Ψ → Fin (r - 1) → ℝ) →L[ℝ] ℂ) := fun c =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj c).comp ((LinearMap.toContinuousLinearMap (anglesL r)).comp (ContinuousLinearMap.proj τ))) with hA
  have hAapp : ∀ c θ, A c θ = (angles (θ τ) c : ℂ) := fun c θ => rfl
  have hc : ∀ c : Fin r, HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => mat x τ a c * Complex.exp (Complex.I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ c b)
      (((mat x τ)⁻¹ c b) • (mat x τ a c • (Complex.exp (Complex.I * (angles ((0 : Ψ → Fin (r - 1) → ℝ) τ) c : ℂ)) • (Complex.I • A c)))) 0 := by
    intro c
    have h1 : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => (angles (θ τ) c : ℂ)) (A c) 0 := (A c).hasStrictFDerivAt
    exact ((h1.const_mul Complex.I).cexp.const_mul (mat x τ a c)).mul_const ((mat x τ)⁻¹ c b)
  have hs := HasStrictFDerivAt.sum (u := Finset.univ) (fun c _ => hc c)
  refine (hs.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext θ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply, torusDer_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hAapp,
      angles_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, smul_eq_mul]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · refine Filter.Eventually.of_forall fun θ => ?_
    simp only [Finset.sum_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
end GlobalTheory.TorusFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZeroStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem _root_.GlobalTheory.T.hasStrictFDerivAt_diagonalTorus_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r), HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  first | exact @GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero | exact GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero | (intros; apply GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodular

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem GlobalTheory.upperTriangular_signForm_diagonal : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  intro r b s hs hdet hup hJ
  classical
  set J : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => (s a : ℂ)) with hJdef
  have hss : ∀ a, (s a : ℂ) * (s a : ℂ) = 1 := by
    intro a; rcases hs a with h | h <;> simp [h]
  have hJJ : J * J = 1 := by
    rw [hJdef, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hss]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hbt : BlockTriangular b id := fun i j hij => hup i j hij
  haveI : Invertible b := b.invertibleOfIsUnitDet hdet
  have hinv : BlockTriangular b⁻¹ id := blockTriangular_inv_of_blockTriangular hbt
  have hright : bᵀ * (J * b.map (starRingEnd ℂ) * J) = 1 := by
    calc bᵀ * (J * b.map (starRingEnd ℂ) * J) = (bᵀ * J * b.map (starRingEnd ℂ)) * J := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have heq : J * b.map (starRingEnd ℂ) * J = (bᵀ)⁻¹ := (Matrix.inv_eq_right_inv hright).symm
  rw [← Matrix.transpose_nonsing_inv] at heq
  have hoff : ∀ a c : Fin r, a < c → b a c = 0 := by
    intro a c hac
    have h1 := congrFun (congrFun heq a) c
    have h2 : (b⁻¹)ᵀ a c = 0 := by
      rw [transpose_apply]; exact hinv hac
    rw [h2, hJdef, mul_diagonal, diagonal_mul] at h1
    simp only [map_apply] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have hsc : (s c : ℂ) ≠ 0 := by rcases hs c with h | h <;> simp [h]
    have : (starRingEnd ℂ) (b a c) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hsa
        · exact h
      · exact absurd h hsc
    simpa using this
  have hdiag : ∀ a c : Fin r, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hoff a c h
    · exact hup a c h
  refine ⟨hdiag, fun a => ?_⟩
  have h1 := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · have hJaa : J a a = (s a : ℂ) := by simp [hJdef]
    rw [mul_diagonal, transpose_apply, map_apply, hJaa] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have h2 : b a a * (starRingEnd ℂ) (b a a) = 1 := by
      have : (s a : ℂ) * (b a a * (starRingEnd ℂ) (b a a)) = (s a : ℂ) * 1 := by
        linear_combination h1
      exact mul_left_cancel₀ hsa this
    rw [Complex.mul_conj] at h2
    have h3 : Complex.normSq (b a a) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    have h4 : 0 ≤ ‖b a a‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖b a a‖ - 1), sq_nonneg (‖b a a‖ + 1)]
  · intro k _ hk
    rw [mul_diagonal, transpose_apply, map_apply, hdiag k a hk]
    simp
  · intro h; exact absurd (Finset.mem_univ a) h
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodularStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem _root_.GlobalTheory.T.upperTriangular_signForm_diagonal_unimodular : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  first | exact @GlobalTheory.upperTriangular_signForm_diagonal | exact GlobalTheory.upperTriangular_signForm_diagonal | (intros; apply GlobalTheory.upperTriangular_signForm_diagonal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalTorusParametrisationOrthonormalFra

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section

namespace GlobalTheory.TorusFrame

theorem gram_mul_of_preserves {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M x : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ u w, hermC τ G (M *ᵥ u) (M *ᵥ w) = hermC τ G u w) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * x) = ReciprocityTheory.ChartRestriction.G.FD.gram τ G x := by
  have hc (a : Fin r) : ReciprocityTheory.ChartRestriction.G.FD.col (M * x) a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col x a := by
    ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply, hc, hM]

theorem torus_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  intro E _ _ _ r X x hx
  refine ⟨fun θ => ⟨torusGL hx θ, GlobalTheory.T.torusElementConjugatedByFrame_mem_specialUnitary E r X x hx θ⟩, torusDer x, ?_, ?_, ?_, ?_, fun θ => GlobalTheory.T.torusTangent_mem_specialUnitaryLie_diagonal E r X x hx θ, ?_⟩
  · intro θ; funext τ
    show ((mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ) = (mat x τ * mat (phaseFrame θ) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]; rfl
  · intro θ θ'
    refine Subtype.ext (funext fun τ => ?_)
    have hp : phaseU ((θ + θ') τ) = phaseU (θ τ) * phaseU (θ' τ) := by
      refine Units.ext ?_
      simp only [phaseU, Units.val_mul, diagonal_mul_diagonal, Pi.add_apply, angles_add, Complex.ofReal_add,
        mul_add, Complex.exp_add]
    simp only [Subgroup.coe_mul, Pi.mul_apply, torusGL, hp]
    group
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    have hph : Continuous fun φ : Fin (r - 1) → ℝ => phaseU φ := by
      refine Units.continuous_iff.2 ⟨Continuous.matrix_diagonal (continuous_pi fun a => ?_),
        Continuous.matrix_diagonal (continuous_pi fun a => ?_)⟩
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a)))
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a))).neg
    exact (continuous_const.mul (hph.comp (continuous_apply τ))).mul continuous_const
  · exact GlobalTheory.T.hasStrictFDerivAt_diagonalTorus_zero E r X.Ψ x
  · rintro g ⟨b, hb, hgb⟩
    have hgx (τ : X.Ψ) : ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat b τ :=
      congrFun hgb τ
    have hdiag (τ : X.Ψ) := GlobalTheory.T.upperTriangular_signForm_diagonal_unimodular r (mat b τ) (fun a => sgn X.p0 a)
      (fun a => by unfold sgn; split_ifs <;> simp) (isUnit_iff_ne_zero.2 (hb τ).1) (fun a c h => (hb τ).2 a c h) (by
        have h1 := gram_mul_of_preserves τ.1 X.Gm _ (mat x τ) ((g.2 τ).2)
        have hJ := hx τ
        rw [gram_eq] at hJ
        rw [hgx τ, gram_eq, gram_eq, transpose_mul, Matrix.map_mul] at h1
        rw [← hJ]; refine Eq.trans ?_ h1; simp only [Matrix.mul_assoc])
    have hbd (τ : X.Ψ) : mat b τ = diagonal fun a => mat b τ a a := by
      ext a c; by_cases h : a = c
      · subst h; simp
      · simp [diagonal_apply_ne _ h, (hdiag τ).1 a c h]
    have hdet (τ : X.Ψ) : ∏ a, mat b τ a a = 1 := by
      have h := congrArg Matrix.det (hgx τ)
      rw [det_mul, det_mul, (g.2 τ).1, one_mul, hbd τ, det_diagonal] at h
      exact (mul_left_cancel₀ (isUnit_det_of_isOrth hx τ).ne_zero (h.symm.trans (mul_one _).symm))
    choose φ hφ using fun τ : X.Ψ => GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one r (fun a => mat b τ a a) (hdiag τ).2 (hdet τ)
    refine ⟨φ, Subtype.ext (funext fun τ => Units.ext ?_)⟩
    show ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) * (mat x τ)⁻¹
    have hD : (diagonal fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) = mat b τ := by
      rw [hbd τ]; congr 1; funext a; exact hφ τ a
    rw [hD, ← hgx τ, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]

end GlobalTheory.TorusFrame
end
end
end
