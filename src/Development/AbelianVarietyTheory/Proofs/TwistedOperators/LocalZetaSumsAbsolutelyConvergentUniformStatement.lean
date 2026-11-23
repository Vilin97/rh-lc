module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosetsStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInertStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGLZetaSumTrivialParameterSubOneLeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormUnitaryZetaSumTrivialBoundSubOneLeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelGLTrivialRep

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.AbsZeta

theorem trivial_isUnitarisable (G : Type) [Group G] : IsUnitarisable (Representation.trivial ℂ G ℂ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => a * starRingEnd ℂ b)
    (fun a a' b => add_mul a a' _) (fun c a b => by simp [smul_eq_mul, mul_assoc])
    (fun a b b' => by simp [mul_add]) (fun c a b => by simp [smul_eq_mul]; ring), ?_, ?_, ?_⟩
  · intro a b
    simp [mul_comm]
  · intro a ha
    simpa [Complex.mul_conj, Complex.normSq_pos] using ha
  · intro g a b
    simp

theorem kerGL_norm {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hz : ‖(z : ℂ)‖ = 1) (hφ : KerGL w N z φ) :
    KerGL w N 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
  intro ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hq : ∀ m : ℤ, (qV E w : ℂ) ^ (-((N : ℂ) / 2) * (m : ℂ)) =
      (((qV E w : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hpos : 0 ≤ (qV E w : ℝ) ^ (-((N : ℝ) / 2) * ((∑ i, |d i| : ℤ) : ℝ)) := by positivity
  beta_reduce
  rw [hφ ϖ hϖ d t ht k₁ hk₁ k₂ hk₂, hq]
  simp [norm_zpow, hz, Complex.norm_real, Real.norm_of_nonneg hpos]
  positivity

end GlobalTheory.FinZeta.AbsZeta


open GlobalTheory.FinZeta.AbsZeta in
theorem GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ B : Multiset ℂˣ, B.card = r ∧ (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) := by
  intro H E _ _ w r t hrt z φ hz hφ
  obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL E w r ℂ (Representation.trivial ℂ _ ℂ) (trivial_isUnitarisable _) 1 one_ne_zero
    (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) (fun h _ => ⟨_, (mul_one _).symm⟩)
  have hs := GlobalTheory.T.unramified_zeta_sum_GL_cosets H E w r t hrt 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) (by simp) (kerGL_norm hz hφ) ℂ
    (Representation.trivial ℂ _ ℂ) 1 B hB hbd LinearMap.id ⟨1, fun g => by simp⟩
  refine ⟨B, ?_, hbd, ?_⟩
  · have hB' := hB
    unfold IsSatVecGL at hB'
    exact hB'.2.2.1
  · simpa using hs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelGLTrivialRepStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasSum_norm_sphericalZetaKernelGL_trivialRep : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ B : Multiset ℂˣ, B.card = r ∧ (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) := by
  first | exact @GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL | exact GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL | (intros; apply GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelUnramifiedUnitary

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaAbsU

theorem hasSum_norm_kerU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α ∧ HasSum (fun a : GU σ r ⧸ KU σ r => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹)) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hK
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : q ≠ 0 := by omega
  obtain ⟨-, -, hS⟩ := GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivial_hyp hU hq0 r
  obtain ⟨x, hx⟩ := hS.exists_vec
  have bound : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r (GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0) := by
    intro i
    have hi := i.2
    have h2 : 2 * i.val + 2 ≤ r := by omega
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hn : ‖(GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0 i : ℂ)‖ = (q : ℝ) ^ ((r : ℝ) - 1 - 2 * (i.val : ℝ)) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam, Units.val_zpow_eq_zpow_val, norm_zpow, Units.val_mk0, Complex.norm_natCast,
        ← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    have hlow : ((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)) = (q : ℝ) ^ (-((r : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
      congr 1
      push_cast
      ring
    rw [hn, hlow, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq]
    have h2' : 2 * (i.val : ℝ) + 2 ≤ r := by exact_mod_cast h2
    have h0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> linarith
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0, bound, ?_⟩
  have hKψ : KerU ϖ q (r + t) 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
    intro d g hg k₁ hk₁ k₂ hk₂
    simp only
    rw [hK d g hg k₁ hk₁ k₂ hk₂]
    simp [norm_zpow, hz]
  have h := GlobalTheory.T.hasSum_unramifiedZetaSum_unitary_inert L ϖ σ q r t hU hrt 1 _ (by simp) hKψ ℂ (GlobalTheory.LGrp.charRep 1) x _ hx bound LinearMap.id
    ⟨‖x‖, fun g => by simp⟩
  have hx0 : x ≠ 0 := hx.1
  have h' := h.mul_right x⁻¹
  simpa [mul_assoc, mul_inv_cancel₀ hx0] using h'

end GlobalTheory.ZetaAbsU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelUnramifiedUnitaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasSum_norm_sphericalZetaKernel_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α ∧ HasSum (fun a : GU σ r ⧸ KU σ r => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹)) := by
  first | exact @GlobalTheory.ZetaAbsU.hasSum_norm_kerU | exact GlobalTheory.ZetaAbsU.hasSum_norm_kerU | (intros; apply GlobalTheory.ZetaAbsU.hasSum_norm_kerU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalZetaSumsAbsolutelyConvergentUniform

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.AbsConv

theorem invGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g, ∀ k ∈ KGL w (n := r), φ (g * k) = φ g := by
  intro E _ _ w r N z φ h g k hk
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV (E := E) w
  obtain ⟨d, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ (mem_Ov_of_isUnifV hϖ) hϖ g
  have htd : (k₁⁻¹ * g * k₂⁻¹ : GL (Fin r) (w.adicCompletion E)).1 = Matrix.diagonal (fun i => ϖ ^ d i) := by
    rw [Units.val_mul, Units.val_mul, e]
    simp [Matrix.mul_assoc]
    rfl
  calc φ (g * k) = φ (k₁ * (k₁⁻¹ * g * k₂⁻¹) * (k₂ * k)) := by congr 1; group
    _ = φ (k₁ * (k₁⁻¹ * g * k₂⁻¹) * k₂) := by
      rw [h ϖ hϖ d _ htd k₁ hk₁ (k₂ * k) (mul_mem hk₂ hk), h ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂]
    _ = φ g := by congr 1; group

theorem invU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q r N : ℕ), IsUnramInv ϖ σ q → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), KerU ϖ q N z φ → ∀ g, ∀ k ∈ KU σ r, φ (g * k) = φ g := by
  intro E _ _ w ϖ σ q r N hU z φ h g k hk
  obtain ⟨d, t, -, htd, k₁, hk₁, k₂, hk₂, rfl⟩ := cartanU hU g
  rw [show k₁ * t * k₂ * k = k₁ * t * (k₂ * k) by group, h d t htd k₁ hk₁ _ (mul_mem hk₂ hk), h d t htd k₁ hk₁ k₂ hk₂]

theorem transport : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ (f : H → ℝ), (∀ h, ∀ k ∈ K', f (h * k) = f h) → ∀ A : ℝ, HasSum (fun a : H ⧸ K' => f a.out) A → HasSum (fun a : G ⧸ K => f (e a.out)) A := by
  intro G H _ _ e K K' hK f hf A hA
  let Φ : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]
    simp)
  have key : ∀ a : G ⧸ K, f (Φ a).out = f (e a.out) := by
    intro a
    have h1 : Φ a = (QuotientGroup.mk (e a.out) : H ⧸ K') := by
      conv_lhs => rw [← Quotient.out_eq a]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' (e a.out)
    rw [h1, hk, hf _ _ k.2]
  have := (Φ.hasSum_iff (f := fun b : H ⧸ K' => f b.out)).2 hA
  simpa [Function.comp_def, key] using this

theorem glSum : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r + 5 ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ A : ℝ, HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => ‖φ a.out‖) A ∧ |A - 1| ≤ 27 ^ r * ((qV E w : ℝ) ^ 2)⁻¹ := by
  intro hP E _ _ w r t ht z φ hz hk
  obtain ⟨B, hc, hb, hs⟩ := GlobalTheory.T.hasSum_norm_sphericalZetaKernelGL_trivialRep hP E w r t (by omega) z φ hz hk
  refine ⟨_, by simpa using Complex.hasSum_re hs, ?_⟩
  have hq2 : 2 ≤ qV E w := one_lt_absNorm w
  have hX : ‖npow w (-((1 + (t : ℂ)) / 2))‖ = (qV E w : ℝ) ^ (-((1 + (t : ℝ)) / 2)) := by
    rw [norm_npow]
    congr 1
    simp
  refine le_trans ?_ (GlobalTheory.T.norm_GL_zetaSum_trivialParameter_sub_one_le (qV E w) hq2 r t ht B hc hb _ hX)
  have := Complex.abs_re_le_norm (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) *
    eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) *
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹) - 1)
  simpa using this

theorem uSum : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r + 5 ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ A : ℝ, HasSum (fun a : GU σ r ⧸ KU σ r => ‖φ a.out‖) A ∧ |A - 1| ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro L _ _ _ ϖ σ q r t hU ht z φ hz hk
  obtain ⟨α, hb, hs⟩ := GlobalTheory.T.hasSum_norm_sphericalZetaKernel_unramifiedUnitary L ϖ σ q r t hU (by omega) z φ hz hk
  refine ⟨_, by simpa using Complex.hasSum_re hs, ?_⟩
  refine le_trans ?_ (GlobalTheory.T.norm_unitaryZetaSum_trivialBound_sub_one_le q r t hU.2.2.2.2.2.1 ht α hb)
  have := Complex.abs_re_le_norm (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) *
    ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1)
  simpa using this

theorem local_place (hP : GlobalTheory.Published.UnramifiedDoublingGL) (D : D7) (V : HSp D) (hr : V.rank = D.R.r)
    (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (hz : ∀ w, ‖(z w : ℂ)‖ = 1) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Gv V v → ℂ) (hφ : IsLocKer V D.R.nV z v φ) :
    ∃ A : ℝ, HasSum (fun a : Gv V v ⧸ Kv V v => ‖φ a.out‖) A ∧
      |A - 1| ≤ 27 ^ D.R.r * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ := by
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hN : D.R.nV = V.rank + D.R.t := by rw [hr]; rfl
  have ht : V.rank + 5 ≤ D.R.t := by rw [hr]; exact D.R.rank_add_five_le
  rw [← hr]
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · rw [hw] at hs
    obtain ⟨⟨e, he⟩, hq⟩ := GlobalTheory.NoExcl.chart V hw hs
    have hk := (hφ w hw).1 hs e he
    rw [hN] at hk
    obtain ⟨A, hA, hb⟩ := glSum hP D.host.E w V.rank D.R.t ht (z w) _ (hz w) hk
    refine ⟨A, ?_, ?_⟩
    · have := transport _ _ e (Kv V v) (KGL w (n := V.rank)) he.2 (fun g => ‖(φ ∘ e.symm) g‖)
        (fun g k hk' => congrArg norm (invGL _ w _ _ _ _ hk g k hk')) A hA
      simpa using this
    · have hq' : (qV D.host.E w : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        rw [show qV D.host.E w = Ideal.absNorm w.asIdeal from rfl, hq]; rfl
      rwa [hq'] at hb
  · rw [hw] at hi
    obtain ⟨c, ϖ, e, hU, he, -, -⟩ := GlobalTheory.LPositivity.exists_inert_chart (isCMExt_host D) (GlobalTheory.NoExcl.isHermND_gram V)
      (SelfDual.isLattice_frameLat V) (SelfDual.isSelfDualAt_frameLat D V v) hw hi
    have hk := (hφ w hw).2 hi c ϖ e hU he
    rw [hN] at hk
    obtain ⟨A, hA, hb⟩ := uSum _ ϖ c (qV D.host.F v) V.rank D.R.t hU ht (z w) _ (hz w) hk
    refine ⟨A, ?_, hb⟩
    have := transport _ _ e (Kv V v) (KU c V.rank) he.2.2 (fun g => ‖(φ ∘ e.symm) g‖)
      (fun g k hk' => congrArg norm (invU _ w ϖ c _ _ _ hU _ _ hk g k hk')) A hA
    simpa using this

theorem absConv_localZeta : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ), (∀ w, ‖(z w : ℂ)‖ = 1) → ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (φ : ∀ v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}, Gv V v.1 → ℂ), (∀ v, IsLocKer V D.R.nV z v.1 (φ v)) → ∃ A : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} → ℝ, Summable (fun v => A v - 1) ∧ ∀ v, HasSum (fun a : Gv V v.1 ⧸ Kv V v.1 => ‖φ v a.out‖) (A v) := by
  intro hP D V hr z hz Sb φ hφ
  choose A hA hB using fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => local_place hP D V hr z hz v.1 (φ v) (hφ v)
  refine ⟨A, ?_, hA⟩
  have hs := (summable_rpow (K := D.host.F) ((Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (σ := 2) (by norm_num)).mul_left (27 ^ D.R.r)
  refine Summable.of_norm_bounded hs fun v => ?_
  rw [Real.norm_eq_abs]
  refine (hB v).trans (le_of_eq ?_)
  congr 1
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

end GlobalTheory.FinZeta.AbsConv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalZetaSumsAbsolutelyConvergentUniformStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localZetaSums_absolutely_convergent_uniform : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ), (∀ w, ‖(z w : ℂ)‖ = 1) → ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (φ : ∀ v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}, Gv V v.1 → ℂ), (∀ v, IsLocKer V D.R.nV z v.1 (φ v)) → ∃ A : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} → ℝ, Summable (fun v => A v - 1) ∧ ∀ v, HasSum (fun a : Gv V v.1 ⧸ Kv V v.1 => ‖φ v a.out‖) (A v) := by
  first | exact @GlobalTheory.FinZeta.AbsConv.absConv_localZeta | exact GlobalTheory.FinZeta.AbsConv.absConv_localZeta | (intros; apply GlobalTheory.FinZeta.AbsConv.absConv_localZeta <;> assumption)
end
end
