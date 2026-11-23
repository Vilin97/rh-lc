module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowFin
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowHt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalSupportCommonDenominator
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
public import Development.WeilBound.ThetaLifts.LeviDeterminants.AdelicThetaSumNormLePolynomialScale
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaSumInvariantRationalUnitary
import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibilityStatement
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowFinal
import Development.WeilBound.ThetaLifts.LeviDeterminants.ContinuousOfMem
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSob
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowTr

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRationalSupportBound

section

@[expose] public section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0
open Grow
theorem weil_rational_support_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C, -, hC⟩ := htBd F E σ n d X W M
  obtain ⟨m₀, hm₀, h₀⟩ := finInv F _ B.ψ hP.base.std Φ hΦ
  obtain ⟨D, hD, hDD⟩ := exists_dual_den F
  refine ⟨D * m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨m, hm, hmC, hb⟩ := hC g h
  refine ⟨D * (m₀ * m), Nat.mul_pos hD (Nat.mul_pos hm₀ hm), ?_, fun ξ hξ i => ?_⟩
  · push_cast
    rw [pow_one, mul_assoc, mul_assoc]
    gcongr
  · rw [Nat.cast_mul D, mul_assoc]
    refine hDD _ fun y => trace_int hP.base.std _ ?_
    let u : AF F := (0, (algebraMap F (AF F) (y : F)).2)
    have hu : IntF u := ⟨rfl, fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v y⟩
    have h0 : IntF (0 : AF F) := ⟨rfl, fun v => by rw [map_zero]; exact zero_mem _⟩
    have key := congrFun (h₀ _ _ _ _ (impl_sOf hP.weil g h) hb (0, Pi.single i u) ⟨fun _ => h0, fun j => by
      by_cases e : j = i
      · subst e; simpa using hu
      · simpa [e] using h0⟩) fun i => algebraMap F (AF F) (ξ i)
    simp only [schr, Prod.smul_mk, smul_zero, add_zero, Pi.zero_apply, zero_mul, mul_zero, dotProduct_smul,
      dotProduct_single] at key
    rw [← mul_right_cancel₀ hξ (key.trans (one_mul _).symm)]
    refine congrArg B.ψ (Prod.ext ?_ ?_)
    · change (0 : Ainf F) = ((m₀ * m : ℕ) : AF F).1 * ((algebraMap F (AF F) (ξ i)).1 * 0)
      rw [mul_zero, mul_zero]
    · rw [map_mul, map_mul, map_natCast, mul_assoc]
      rfl
end PositivityTheory.ThKF0
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaModerateGrowth

section

@[expose] public section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0
def ArchBd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k
theorem norm_theta_le_mul_ht_pow_of_isPair (harch : _root_.PositivityTheory.ThKF0.ArchBd_k) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := theta_sum_norm_bound_denominator
  have hfin := _root_.PositivityTheory.ThKF0.weil_rational_support_bound
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring
end PositivityTheory.ThKF0
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaSumRationalPairInvariant

section

@[expose] public section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
noncomputable section
namespace PositivityTheory.ThKF0
theorem thetaSum_rational_pair_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := rat_det_ne_zero_of_map X.J (B.emb w).1 (rat_det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine rat_det_ne_zero_of_map W.J (B.emb w).1 fun h0 => rat_det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact darboux_coordinates_rational_exist F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ
end PositivityTheory.ThKF0
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicOfK

section

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
namespace PositivityTheory.ThKF0
theorem thetaBasic_of_k (harch : _root_.PositivityTheory.ThKF0.ArchBd_k) : _root_.GlobalTheory.ThK.ThetaBasic_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := (GlobalTheory.T.theta_distribution_nonzero_admissible F (Fin n × Fin d)).2.1
  refine ⟨fun Φ hΦ => ⟨?_, ?_, _root_.PositivityTheory.ThKF0.norm_theta_le_mul_ht_pow_of_isPair harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact _root_.PositivityTheory.ThKF0.thetaSum_rational_pair_invariant F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm
end PositivityTheory.ThKF0
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchwartzDecayUniform

section

@[expose] public section



section
noncomputable section
namespace PositivityTheory.ThKF0.Grow
open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
open GlobalTheory.LFun GlobalTheory.ThK in
theorem schwartz_decay_uniform (hA : HtBd) (hF : FinInv) (hS : Sob) (hT : TrBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  obtain ⟨C, -, hC⟩ := hA F E σ n d X W M
  obtain ⟨C', k, -, h⟩ := weighted hF hS hT hP.base.std hΦ N
  refine ⟨C' * C ^ k, k, fun g g' x => ?_⟩
  obtain ⟨m, h1, h2, h3⟩ := hC g g'
  rw [mul_assoc, ← mul_pow]
  exact h _ _ m _ h1 h2 (impl_sOf hP.weil g g') h3 x
end PositivityTheory.ThKF0.Grow
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilSchwartzDecayBound

section

@[expose] public section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
theorem PositivityTheory.ThKF0.weil_schwartz_decay_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k :=
  _root_.PositivityTheory.ThKF0.Grow.schwartz_decay_uniform PositivityTheory.ThKF0.Grow.htBd PositivityTheory.ThKF0.Grow.finInv
    (PositivityTheory.ThKF0.Grow.sob_of PositivityTheory.ThKF0.Grow.derivOK) PositivityTheory.ThKF0.Grow.trBd
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicKAlt

section

@[expose] public section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0
theorem thetaBasic_k : _root_.GlobalTheory.ThK.ThetaBasic_k := _root_.PositivityTheory.ThKF0.thetaBasic_of_k _root_.PositivityTheory.ThKF0.weil_schwartz_decay_bound
end PositivityTheory.ThKF0
end
end
end
