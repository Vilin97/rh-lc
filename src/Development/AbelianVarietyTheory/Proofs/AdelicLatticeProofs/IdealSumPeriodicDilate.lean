module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Fourier.FourierTransform
public import Formalism.LatticeTheta.ThetaShiftInversion
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
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
public import Formalism.LatticeTheta.Statement
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ZlatticeTsumDilateSubIntegralLeRapid

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open scoped FourierTransform RealInnerProductSpace SchwartzMap

namespace GlobalTheory

theorem fourier_comp_smul_of_pos {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (f : V → ℂ) {t : ℝ} (ht : 0 < t)
    (w : V) :
    (𝓕 (fun x => f (t • x)) : V → ℂ) w
      = (((t ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) * (𝓕 f : V → ℂ) (t⁻¹ • w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have h := Measure.integral_comp_smul (volume : Measure V)
    (fun u : V => cexp (((-2 * Real.pi * ⟪u, t⁻¹ • w⟫ : ℝ) : ℂ) * I) • f u) t
  rw [abs_of_pos (by positivity), Complex.real_smul] at h
  rw [← h]
  congr 1
  ext v
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc t, mul_inv_cancel₀ ht.ne', one_mul]

theorem latticeSum_dilate_sub_integral_le (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (A : ℕ) :
    ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 →
      ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) /
        ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  obtain ⟨hD, -⟩ := Formalism.H.dualIsLattice V L
  set d := Module.finrank ℝ V with hd
  set k := A + d + Module.finrank ℤ (Formalism.H.dual L) + 1 with hk
  set F : 𝓢(V, ℂ) := hc.toSchwartzMap hf with hF
  have hFf : (F : V → ℂ) = f := rfl
  obtain ⟨C, hC0, hC⟩ := (𝓕 F : 𝓢(V, ℂ)).decay k 0
  have hs := ZLattice.summable_norm_pow_inv (Formalism.H.dual L) k (by omega)
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  refine ⟨(ZLattice.covolume L)⁻¹ * (C * ∑' y : Formalism.H.dual L, ‖y‖⁻¹ ^ k), ?_⟩
  intro x₀ t ht ht1
  have hft : ContDiff ℝ ∞ (fun x : V => f (t • x)) := hf.comp (contDiff_const_smul t)
  have hct : HasCompactSupport (fun x : V => f (t • x)) :=
    hc.comp_homeomorph (Homeomorph.smulOfNeZero t ht.ne')
  obtain ⟨G, hG⟩ : ∃ G : 𝓢(V, ℂ), (G : V → ℂ) = fun x : V => f (t • x) :=
    ⟨hct.toSchwartzMap hft, rfl⟩
  obtain ⟨h1, h2⟩ := Formalism.H.poissonSchwartz V L G x₀
  rw [hG] at h1 h2
  rw [h2.tsum_eq, h1.tsum_eq_add_tsum_ite 0]
  have h0 : (𝓕 (fun x : V => f (t • x)) : V → ℂ) ((0 : Formalism.H.dual L) : V) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪((0 : Formalism.H.dual L) : V), x₀⟫ : ℝ))
      = (((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
    rw [fourier_comp_smul_of_pos f ht, Real.fourier_eq']
    simp [hd]
  rw [h0, mul_add]
  have h3 : ∀ S : ℂ, (ZLattice.covolume L : ℂ)⁻¹ * ((((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x) + S -
      (∫ x, f x) / ((ZLattice.covolume L * t ^ d : ℝ) : ℂ) = S := by
    intro S
    push_cast
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [h3, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcov.le,
    mul_assoc (ZLattice.covolume L volume)⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcov.le)
  rw [← tsum_mul_left, ← tsum_mul_right]
  refine tsum_of_norm_bounded (((hs.mul_left C).mul_right (t ^ A)).hasSum) ?_
  intro y
  split_ifs with hy
  · rw [norm_zero]; positivity
  have hn : 0 < ‖(y : V)‖ := norm_pos_iff.2 (fun h => hy (Subtype.ext h))
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(y : V), x₀⟫ : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, he, mul_one, fourier_comp_smul_of_pos f ht, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have h4 := hC (t⁻¹ • (y : V))
  rw [norm_iteratedFDeriv_zero, _root_.norm_smul, Real.norm_of_nonneg (by positivity),
    SchwartzMap.fourier_coe, hFf] at h4
  change _ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ A
  have h5 : ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ k := by
    rw [mul_comm, ← le_div_iff₀ (by positivity)] at h4
    refine h4.trans_eq ?_
    rw [mul_pow, inv_pow, inv_pow]
    field_simp
  have h6 : t ^ k ≤ t ^ (A + d) := pow_le_pow_of_le_one ht.le ht1 (by omega)
  calc (t ^ d)⁻¹ * ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖
      ≤ (t ^ d)⁻¹ * (C * ‖(y : V)‖⁻¹ ^ k * t ^ (A + d)) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by rw [pow_add t A d]; field_simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ZlatticeTsumDilateSubIntegralLeRapidStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) / ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  exact @GlobalTheory.latticeSum_dilate_sub_integral_le
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LatticeSumDilateHaarAsymptotic

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem integral_div_covolume_eq_of_haar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ ν : Measure V)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (f : V → ℂ) (s : ℝ) :
    (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * s : ℝ) : ℂ) =
      (∫ x, f x ∂ν) / ((ZLattice.covolume L ν * s : ℝ) : ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : μ = 0 := by simpa using hc
    exact (NeZero.ne μ) this
  let b := Module.Free.chooseBasis ℤ L
  have h1 := ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)
  have h2 := ZLattice.covolume_eq_measure_fundamentalDomain L ν
    (ZLattice.isAddFundamentalDomain b ν)
  have h3 : ZLattice.covolume L μ = (c : ℝ) * ZLattice.covolume L ν := by
    rw [h1, h2]
    conv_lhs => rw [hc]
    simp [Measure.real]
  have h4 : ∫ x, f x ∂μ = (c : ℂ) * ∫ x, f x ∂ν := by
    conv_lhs => rw [hc]
    rw [integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
  have hc1 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [h3, h4]
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ hc1]

theorem lattice_sum_dilate_haar :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  intro V _ _ _ _ _ μ _ L _ _ f hf hs A
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V := toEuclidean.symm
  let ν : Measure V := (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).map e
  have : ν.IsAddHaarMeasure := ContinuousLinearEquiv.isAddHaarMeasure_map e _
  have hmp : MeasurePreserving e volume ν := ⟨e.continuous.measurable, rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid _ (ZLattice.comap ℝ L e.toLinearMap) (f ∘ e)
    (hf.comp e.contDiff) (hs.comp_homeomorph e.toHomeomorph) A
  refine ⟨C, fun x₀ t ht ht1 => ?_⟩
  have h := hC (e.symm x₀) t ht ht1
  rw [ZLattice.covolume_comap L ν volume hmp, finrank_euclideanSpace_fin] at h
  have hi : ∫ x, (f ∘ e) x = ∫ x, f x ∂ν :=
    (hmp.integral_comp e.toHomeomorph.measurableEmbedding f)
  have hsum : ∑' l : ZLattice.comap ℝ L e.toLinearMap,
      (f ∘ e) (t • ((l : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) + e.symm x₀)) =
      ∑' l : L, f (t • ((l : V) + x₀)) := by
    let q : ZLattice.comap ℝ L e.toLinearMap ≃ L :=
      e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
    rw [← q.tsum_eq]
    refine tsum_congr fun l => ?_
    have : ((q l : L) : V) = e l := rfl
    simp [this]
  rw [hi, hsum] at h
  rw [integral_div_covolume_eq_of_haar μ ν L f]
  exact h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LatticeSumDilateHaarAsymptoticStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.lattice_sum_dilate_haar_asymptotic : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  exact @GlobalTheory.lattice_sum_dilate_haar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealSumPeriodicDilate

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.IdealSum

theorem tsum_ideal_eq_sum_classes {R : Type} [CommRing R] (m b : Ideal R) [Fintype (R ⧸ m)]
    (hbm : b ⊔ m = ⊤) (s : R ⧸ m → R) (hsb : ∀ r, s r ∈ b)
    (hs : ∀ r, Ideal.Quotient.mk m (s r) = r) (ψ g : R → ℂ)
    (hψ : ∀ a b, a - b ∈ m → ψ a = ψ b) (hg : Summable fun α : b => ψ α * g α) :
    ∑' α : b, ψ α * g α = ∑ r : R ⧸ m, ψ (s r) * ∑' β : ↥(b * m), g ((β : R) + s r) := by
  have hco : IsCoprime b m := Ideal.isCoprime_iff_sup_eq.2 hbm
  have hl : ∀ x ∈ b * m, x ∈ b := fun x hx => (Ideal.mul_le_inf hx).1
  have hr : ∀ x ∈ b * m, x ∈ m := fun x hx => (Ideal.mul_le_inf hx).2
  obtain ⟨φ, hval⟩ : ∃ φ : (R ⧸ m) × ↥(b * m) → b, ∀ p, (φ p).1 = p.2.1 + s p.1 :=
    ⟨fun p => ⟨p.2.1 + s p.1, b.add_mem (hl _ p.2.2) (hsb _)⟩, fun _ => rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨r, β⟩ ⟨r', β'⟩ h
      have h1 : (β : R) + s r = β' + s r' := by
        have h0 := congrArg Subtype.val h
        rwa [hval, hval] at h0
      have h2 := congrArg (Ideal.Quotient.mk m) h1
      have hβ : Ideal.Quotient.mk m (β : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β.2)
      have hβ' : Ideal.Quotient.mk m (β' : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β'.2)
      rw [map_add (f := _), map_add (f := _), hs, hs, hβ, hβ', zero_add, zero_add] at h2
      subst h2
      rw [Subtype.ext (add_right_cancel h1)]
    · rintro ⟨a, ha⟩
      have hmem : a - s (Ideal.Quotient.mk m a) ∈ b * m := by
        rw [Ideal.mul_eq_inf_of_isCoprime hco]
        exact Ideal.mem_inf.2 ⟨b.sub_mem ha (hsb _), Ideal.Quotient.eq.1 (hs _).symm⟩
      refine ⟨(Ideal.Quotient.mk m a, ⟨a - s (Ideal.Quotient.mk m a), hmem⟩), Subtype.ext ?_⟩
      rw [hval]
      exact sub_add_cancel _ _
  have h1 : ∑' p, ψ (φ p) * g (φ p) = ∑' α : b, ψ α * g α :=
    (Equiv.ofBijective φ hφ).tsum_eq (fun α : b => ψ α * g α)
  have h2 : Summable fun p => ψ (φ p) * g (φ p) := hg.comp_injective hφ.1
  have h3 : ∑' p, ψ (φ p) * g (φ p) = ∑' r, ∑' β, ψ (φ (r, β)) * g (φ (r, β)) :=
    h2.tsum_prod
  rw [← h1, h3, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun β => ?_
  rw [hval]
  rw [hψ ((β : R) + s r) (s r) (by rw [add_sub_cancel_right]; exact hr _ β.2)]

theorem finite_support_dilate (K : Type) [Field K] [NumberField K] (f : mixedSpace K → ℂ)
    (hf : HasCompactSupport f) (t : ℝ) (ht : 0 < t) :
    {α : 𝓞 K | f (t • mixedEmbedding K (α : K)) ≠ 0}.Finite := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : mixedSpace K)).1
    hf.isCompact.isBounded
  let I := FractionalIdeal.mk0 K (1 : (Ideal (𝓞 K))⁰)
  have hd : DiscreteTopology (idealLattice K I).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (idealLattice K I))
  have hfin : (Metric.closedBall (0 : mixedSpace K) (r / t) ∩
      (idealLattice K I : Set (mixedSpace K))).Finite :=
    Metric.finite_isBounded_inter_isClosed
      (isDiscrete_iff_discreteTopology.2 hd)
      Metric.isBounded_closedBall
      (((idealLattice K I).toAddSubgroup).isClosed_of_discreteTopology)
  have hinj : Function.Injective fun α : 𝓞 K => mixedEmbedding K (α : K) :=
    (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective
  refine (hfin.preimage hinj.injOn).subset fun α hα => ⟨?_, ?_⟩
  · have := hr (subset_tsupport f hα)
    rw [mem_closedBall_zero_iff, _root_.norm_smul, Real.norm_of_nonneg ht.le] at this
    rw [mem_closedBall_zero_iff, le_div_iff₀ ht, mul_comm]
    exact this
  · refine (mem_idealLattice K I).2 ⟨(α : K), ?_, rfl⟩
    simp [I]

theorem tsum_idealLattice (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰)
    (F : mixedSpace K → ℂ) :
    ∑' l : idealLattice K (FractionalIdeal.mk0 K J), F l =
      ∑' β : ↥(J.1), F (mixedEmbedding K ((β : 𝓞 K) : K)) := by
  let φ : ↥(J.1) → idealLattice K (FractionalIdeal.mk0 K J) := fun β =>
    ⟨mixedEmbedding K ((β : 𝓞 K) : K), (mem_idealLattice K _).2 ⟨((β : 𝓞 K) : K), by
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ β.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      exact Subtype.ext (RingOfIntegers.coe_injective
        (mixedEmbedding_injective K (congrArg Subtype.val h)))
    · rintro ⟨l, hl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).1 hl
      rw [FractionalIdeal.coe_mk0] at hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ((Equiv.ofBijective φ hφ).tsum_eq (fun l => F l)).symm

theorem ideal_sum_periodic_dilate : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (ψ : 𝓞 K → ℂ) (f : mixedSpace K → ℂ), m ≠ ⊥ → (∀ a b, a - b ∈ m → ψ a = ψ b) → ContDiff ℝ ∞ f → HasCompactSupport f → ∃ κ : ℂ, ∀ b : Ideal (𝓞 K), b ≠ ⊥ → b ⊔ m = ⊤ → ∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' α : b, ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K)) - κ / (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  intro K _ _ m ψ f hm hψ hf hfc
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm
  haveI : Fintype (𝓞 K ⧸ m) := Fintype.ofFinite _
  set D : ℝ := 2⁻¹ ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)| with hD
  refine ⟨(∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) /
    (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ), fun b hb hbm A => ?_⟩
  have hrep : ∀ r : 𝓞 K ⧸ m, ∃ x ∈ b, Ideal.Quotient.mk m x = r := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (hbm ▸ Submodule.mem_top : a ∈ b ⊔ m)
    exact ⟨x, hx, by rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hy, add_zero]⟩
  choose s hsb hs using hrep
  let J : (Ideal (𝓞 K))⁰ := ⟨b * m, mem_nonZeroDivisors_iff_ne_zero.2 (mul_ne_zero hb hm)⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.lattice_sum_dilate_haar_asymptotic (mixedSpace K) volume
    (idealLattice K (FractionalIdeal.mk0 K J)) f hf hfc A
  refine ⟨(∑ r : 𝓞 K ⧸ m, ‖ψ (s r)‖) * C, fun t ht ht1 => ?_⟩
  have hsum : Summable fun α : b => ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K)) := by
    refine summable_of_hasFiniteSupport ?_
    refine ((finite_support_dilate K f hfc t ht).preimage
      (Subtype.val_injective (p := fun x => x ∈ b)).injOn).subset fun α hα => ?_
    exact right_ne_zero_of_mul hα
  rw [tsum_ideal_eq_sum_classes m b hbm s hsb hs ψ
    (fun α => f (t • mixedEmbedding K (α : K))) hψ hsum]
  have hout : ∀ r : 𝓞 K ⧸ m, ψ (Quotient.out r) = ψ (s r) := fun r =>
    hψ _ _ (Ideal.Quotient.eq.1 ((Ideal.Quotient.mk_out r).trans (hs r).symm))
  have hcov : ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume =
      (Ideal.absNorm b : ℝ) * ((Ideal.absNorm m : ℝ) * D) := by
    rw [covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, hD]
    simp only [J, map_mul]
    push_cast
    ring
  have key : (∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) /
      (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ) /
      (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ) =
      ∑ r : 𝓞 K ⧸ m, ψ (s r) * ((∫ x, f x) /
        ((ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume *
          t ^ Module.finrank ℝ (mixedSpace K) : ℝ) : ℂ)) := by
    rw [← Finset.sum_mul, hcov, mixedEmbedding.finrank, div_div, mul_div_assoc]
    simp only [hout]
    congr 2
    push_cast
    ring
  rw [key, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun r _ => ?_
  rw [← mul_sub, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := hC (mixedEmbedding K (s r : K)) t ht ht1
  rw [tsum_idealLattice K J (fun l => f (t • (l + mixedEmbedding K (s r : K))))] at h
  have hβ : ∀ β : ↥(b * m), mixedEmbedding K (((β : 𝓞 K) + s r : 𝓞 K) : K) =
      mixedEmbedding K ((β : 𝓞 K) : K) + mixedEmbedding K (s r : K) := fun β => by
    rw [← map_add (f := _)]
    rfl
  simp only [hβ]
  exact h

end GlobalTheory.IdealSum
end
end
