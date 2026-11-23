module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTestStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistanceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantIntegrable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ShellSumMajorant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableAndTsumLeOfBoxCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBound

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem decE_dOp_le_floor {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (h : ℝ)
    (hh : 32 * (n : ℝ) ^ 2 * Real.sqrt (rkR ε) ≤ h) (g : UJ ε) :
    decE (rkR ε) h (dOp (uMat g)) ≤ Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊dOp (uMat g)⌋₊ : ℝ))) := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | hq
  · simp [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g, decE]
  · obtain ⟨ha, hb, -⟩ := shell_sum_majorant n (rkR ε) h hn hq hh
    have hp : 0 ≤ dOp (uMat g) := ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    refine (ha (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Set.mem_Ici.2 hp) (Nat.floor_le hp)).trans ?_
    refine (hb _).trans (le_of_eq ?_)
    congr 2
    ring

theorem norm_phe_le_floor (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hn : 1 ≤ B.I.n) (hl : LocDec B h) (hb : HBig B 32 h) (g : B.I.GA) :
    ‖phe B d g‖ ≤ ((∏ v, d v) * (B.e 1).re) *
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
  obtain ⟨-, he0, he, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have h1 : ‖∏ v, ⟪B.w v, B.σ v (uMat (g.1 v)) (B.w v)⟫_ℂ‖ ≤
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ =>
      (hl v _).trans (decE_dOp_le_floor hn _ h (hb v) _)
  unfold phe ph
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hd0, mul_assoc, mul_assoc,
    mul_comm (B.e 1).re]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (he _) (norm_nonneg _) ((norm_nonneg _).trans h1)) hd0

theorem kernel_abs_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  intro B d h hd hn hl hb x y
  obtain ⟨-, he0, -, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have ht := (GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties B.I hn).1
  have hx := ht x
  have hy := ht y
  have hn' : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have ha : (1 : ℝ) ≤ 2 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have hexp : (2 : ℝ) ≤ Real.exp (2 * (B.I.n : ℝ) ^ 2) := by
    have := Real.add_one_le_exp (2 * (B.I.n : ℝ) ^ 2)
    linarith
  have hA : 0 ≤ (3 * Real.sqrt B.I.n / (tau1 B.I x * tau1 B.I y)) ^ (2 * B.I.n ^ 2 * B.I.f) := by positivity
  have hc : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd0 he0
  obtain ⟨hs, hle⟩ := GlobalTheory.summable_and_tsum_le_of_box_count (InfinitePlace B.I.F) B.I.GFset
    (fun γ v => dOp (uMat ((x⁻¹ * γ.1 * y).1 v))) (fun γ => ‖phe B d (x⁻¹ * γ.1 * y)‖)
    (2 * (B.I.n : ℝ) ^ 2) _ _ hA hc
    (by rw [Real.exp_neg, one_div]; exact inv_anti₀ two_pos hexp)
    (fun γ v => ((GlobalTheory.Count.Cartan.cartan_distances B.I.n _).2.1 _ 1 hn).1)
    (fun γ => ⟨norm_nonneg _, norm_phe_le_floor B d h hd hn hl hb _⟩)
    (by
      intro r hr
      obtain ⟨hf, hcnt⟩ := GlobalTheory.T.count_rational_elements_bounded_distance B.I x y r hn hr
      have hsub : Subtype.val '' {γ : B.I.GFset | ‖phe B d (x⁻¹ * γ.1 * y)‖ ≠ 0 ∧
            ∀ v, dOp (uMat ((x⁻¹ * γ.1 * y).1 v)) ≤ r v} ⊆
          {γ ∈ B.I.GFset | (x⁻¹ * γ * y).2 ∈ B.I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v} := by
        rintro _ ⟨γ, ⟨h1, h2⟩, rfl⟩
        refine ⟨γ.2, B.e_adm.2.2.2.2.1 _ fun h0 => h1 ?_, h2⟩
        unfold phe
        rw [h0, mul_zero, norm_zero]
      refine ⟨Set.Finite.of_finite_image (hf.subset hsub) Subtype.val_injective.injOn, le_trans ?_ hcnt⟩
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
      exact_mod_cast Set.ncard_le_ncard hsub hf)
  refine ⟨hs, hle.trans ?_⟩
  have hcard : Fintype.card (InfinitePlace B.I.F) ≤ B.I.f := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank B.I.F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces B.I.F
    unfold AutInst.f
    omega
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hcard) (mul_nonneg hc hA)).trans
    (le_of_eq ?_)
  unfold kerC
  rw [div_eq_mul_inv, mul_pow (3 * Real.sqrt B.I.n)]
  ring

end GlobalTheory.Dec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBoundStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.discreteSeriesKernel_summable_with_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  first | exact @GlobalTheory.Dec.kernel_abs_bound | exact GlobalTheory.Dec.kernel_abs_bound | (intros; apply GlobalTheory.Dec.kernel_abs_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergenceProperties

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelConv

theorem coef_inv {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) (g : UJ ε) :
    ⟪w, σ (uMat g⁻¹) w⟫_ℂ = star ⟪w, σ (uMat g) w⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hnorm, -⟩ := hσ
  have hg : uMat g ∈ UJset ε := g.2
  have hgi : uMat g⁻¹ ∈ UJset ε := (g⁻¹).2
  have hone : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    simp
  have hback : σ (uMat g) (σ (uMat g⁻¹) w) = w := by
    have := congrArg (fun T : H →L[ℂ] H => T w) (hmul _ hg _ hgi)
    simp only [hone, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ (uMat g) : H →ₗ[ℂ] H), norm_map' := hnorm _ hg }
  have key : ⟪w, σ (uMat g⁻¹) w⟫_ℂ = ⟪σ (uMat g) w, w⟫_ℂ := by
    rw [← L.inner_map_map w (σ (uMat g⁻¹) w)]
    show ⟪σ (uMat g) w, σ (uMat g) (σ (uMat g⁻¹) w)⟫_ℂ = _
    rw [hback]
  rw [key, ← inner_conj_symm]
  rfl

theorem phe_inv (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) (x : B.I.GA) :
    phe B d x⁻¹ = star (phe B d x) := by
  have he : B.e x⁻¹.2 = star (B.e x.2) := B.e_adm.2.2.1 x.2
  have hp : ∏ v, ⟪B.w v, B.σ v (uMat (x⁻¹.1 v)) (B.w v)⟫_ℂ =
      star (∏ v, ⟪B.w v, B.σ v (uMat (x.1 v)) (B.w v)⟫_ℂ) := by
    rw [star_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    show ⟪B.w v, B.σ v (uMat (x.1 v)⁻¹) (B.w v)⟫_ℂ = _
    exact coef_inv (hd v).2.1.2.2.1 (B.w v) (x.1 v)
  unfold phe ph
  rw [he, hp]
  simp only [star_mul', star_star]
  rw [show star ((∏ v, d v : ℝ) : ℂ) = ((∏ v, d v : ℝ) : ℂ) from Complex.conj_ofReal _]

theorem kern_eq (I : AutInst) (Γ : Subgroup I.GA) (hΓ : (Γ : Set I.GA) = I.GFset) (φ : I.GA → ℂ) (x y : I.GA) :
    kern I φ x y = ∑' γ : Γ, φ (x⁻¹ * γ.1 * y) := by
  unfold kern
  exact ((Equiv.subtypeEquivRight (fun a => by rw [← hΓ, SetLike.mem_coe]) : Γ ≃ I.GFset).tsum_eq
    (fun γ : I.GFset => φ (x⁻¹ * γ.1 * y))).symm

theorem kern_invariant (I : AutInst) (φ : I.GA → ℂ) (γ : I.GA) (hγ : γ ∈ I.GFset) (x y : I.GA) :
    kern I φ (γ * x) y = kern I φ x y ∧ kern I φ x (γ * y) = kern I φ x y := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  have hγΓ : γ ∈ GlobalTheory.RatDiscrete.ratSub I := hγ
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, kern_eq I _ hΓ]
  constructor
  · refine ((Equiv.mulLeft (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ ((γ * x)⁻¹ * δ.1 * y))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]
  · refine ((Equiv.mulRight (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)⁻¹).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (x⁻¹ * δ.1 * (γ * y)))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]

theorem kern_symm (I : AutInst) (φ : I.GA → ℂ) (hφ : ∀ x, φ x⁻¹ = star (φ x)) (x y : I.GA) :
    kern I φ y x = star (kern I φ x y) := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, tsum_star]
  refine ((Equiv.inv (GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
    (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (y⁻¹ * δ.1 * x))).symm.trans ?_
  congr 1; funext δ
  rw [← hφ]
  simp [mul_assoc]

theorem kernelA : KernelA := by
  unfold KernelA
  intro B d h hd hn hL hH
  refine ⟨GlobalTheory.T.discreteSeriesKernel_summable_with_bound B d h hd hn hL hH, GlobalTheory.T.continuous_automorphicKernel_discreteSeriesTest B d h hd hn hL hH, ?_, ?_⟩
  · intro γ hγ x y
    exact kern_invariant B.I (phe B d) γ hγ x y
  · intro x y
    exact kern_symm B.I (phe B d) (phe_inv B d hd) x y

end GlobalTheory.KernelConv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergencePropertiesStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.automorphicKernel_convergence_properties : KernelA := by
  first | exact @GlobalTheory.KernelConv.kernelA | exact GlobalTheory.KernelConv.kernelA | (intros; apply GlobalTheory.KernelConv.kernelA <;> assumption)
end
end
