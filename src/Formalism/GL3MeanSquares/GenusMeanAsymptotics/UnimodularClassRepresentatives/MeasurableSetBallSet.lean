module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthBasisMem
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VolumeNormSqLeOne

section

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallC

theorem volume_normSq_le_one (M : ℕ) :
    volume {x : Fin M → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} =
      ENNReal.ofReal (Real.pi ^ M / (M.factorial : ℝ)) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have e : {x : Fin 0 → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} = Set.univ := by
      ext x; simp
    rw [e, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
    simp
  · haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    have h := Complex.volume_sum_rpow_le (Fin M) (p := 2) one_le_two 1
    have hset : {x : Fin M → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} =
        {x : Fin M → ℂ | (∑ i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_one]
      simp only [Real.rpow_two, Complex.normSq_eq_norm_sq]
    rw [hset, h, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
    congr 1
    have e1 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
    have e2 : 2 * (M : ℝ) / 2 + 1 = (M : ℝ) + 1 := by ring
    rw [e1, e2, Real.Gamma_two, mul_one, Real.Gamma_nat_eq_factorial]

def ell {M : ℕ} (a : Fin M → ℝ) : Set (Fin M → ℂ) := {z | ∑ i, a i * Complex.normSq (z i) ≤ 1}

variable {M : ℕ} (a : Fin M → ℝ)

theorem mem_ell {z : Fin M → ℂ} : z ∈ ell a ↔ ∑ i, a i * Complex.normSq (z i) ≤ 1 := Iff.rfl

theorem isClosed_ell : IsClosed (ell a) := by
  unfold ell
  exact isClosed_le (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply i))) continuous_const

variable {a}

theorem volume_ell (ha : ∀ i, 0 < a i) :
    volume (ell a) = ENNReal.ofReal (Real.pi ^ M / (M.factorial : ℝ) / ∏ i, a i) := by
  let g : Fin M → (ℂ →ₗ[ℝ] ℂ) := fun i => Real.sqrt (a i) • LinearMap.id
  let f : (Fin M → ℂ) →ₗ[ℝ] (Fin M → ℂ) := LinearMap.pi fun i => (g i) ∘ₗ LinearMap.proj i
  have hf : ∀ z i, f z i = (Real.sqrt (a i) : ℂ) * z i := by
    intro z i
    simp [f, g, Complex.real_smul]
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [g, LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
    exact Real.sq_sqrt (ha i).le
  have hs : ∀ z, ∑ i, Complex.normSq (f z i) = ∑ i, a i * Complex.normSq (z i) := by
    intro z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (ha i).le]
  have hpre : ell a = f ⁻¹' {x | ∑ i, Complex.normSq (x i) ≤ 1} := by
    ext z
    simp only [ell, Set.mem_setOf_eq, Set.mem_preimage, hs]
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  rw [hpre, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact hprod.ne'),
    volume_normSq_le_one, hdet, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hprod)]
  ring

theorem convex_ell (ha : ∀ i, 0 < a i) : Convex ℝ (ell a) := by
  intro x hx y hy s t hs ht hst
  simp only [ell, Set.mem_setOf_eq] at hx hy ⊢
  have key : ∀ i, a i * Complex.normSq ((s • x + t • y) i) ≤
      s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i)) := by
    intro i
    have h1 : Complex.normSq ((s • x + t • y) i) ≤
        s * Complex.normSq (x i) + t * Complex.normSq (y i) := by
      simp only [Pi.add_apply, Pi.smul_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      have ht' : t = 1 - s := by linarith
      subst ht'
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((x i).re - (y i).re)),
        mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((x i).im - (y i).im))]
    calc a i * Complex.normSq ((s • x + t • y) i)
        ≤ a i * (s * Complex.normSq (x i) + t * Complex.normSq (y i)) :=
          mul_le_mul_of_nonneg_left h1 (ha i).le
      _ = s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i)) := by ring
  calc ∑ i, a i * Complex.normSq ((s • x + t • y) i)
      ≤ ∑ i, (s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = s * ∑ i, a i * Complex.normSq (x i) + t * ∑ i, a i * Complex.normSq (y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ s * 1 + t * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hst]

theorem isBounded_ell (ha : ∀ i, 0 < a i) : Bornology.IsBounded (ell a) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨∑ i, (1 + (a i)⁻¹), fun z hz => ?_⟩
  rw [mem_closedBall_zero_iff]
  simp only [ell, Set.mem_setOf_eq] at hz
  have hnn : ∀ j, 0 ≤ 1 + (a j)⁻¹ := fun j => add_nonneg zero_le_one (inv_nonneg.mpr (ha j).le)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hnn i)).mpr fun i => ?_
  have hi : a i * Complex.normSq (z i) ≤ 1 :=
    le_trans (Finset.single_le_sum (f := fun j => a j * Complex.normSq (z j))
      (fun j _ => mul_nonneg (ha j).le (Complex.normSq_nonneg _)) (Finset.mem_univ i)) hz
  have h2 : Complex.normSq (z i) ≤ (a i)⁻¹ := by
    rw [← one_div, le_div_iff₀ (ha i), mul_comm]
    exact hi
  rw [Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖z i‖ ≤ 1 + (a i)⁻¹ := by nlinarith [sq_nonneg (‖z i‖ - 1)]
  exact h3.trans (Finset.single_le_sum (f := fun j => 1 + (a j)⁻¹) (fun j _ => hnn j)
    (Finset.mem_univ i))

end Formalism.HermitianLattices.Ext.L3.BallC
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FundamentalDomainPiBasis

section

@[expose] public section

open NumberField NumberField.mixedEmbedding MeasureTheory Module

open scoped Classical


set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallC

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]

def psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    (ι → mixedSpace K) ≃ₗ[ℝ] ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) where
  toFun y := fun w i => (y i).2 w
  invFun z := fun i => (fun w => isEmptyElim w, fun w => z w i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext i
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv z := rfl

theorem psi_apply [IsEmpty {w : InfinitePlace K // w.IsReal}] (y : ι → mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) : psi K ι y w i = (y i).2 w := rfl

theorem measurePreserving_psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (psi K ι) volume volume := by
  let e := (psi K ι).toContinuousLinearEquiv
  have he : ∀ y, e y = psi K ι y := fun y => rfl
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e volume = volume
  have : (Measure.map e volume).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let K₀ : TopologicalSpace.PositiveCompacts
      ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) :=
    ⟨⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩, by
      change (interior (Metric.closedBall 0 1)).Nonempty
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0, Metric.mem_ball_self one_pos⟩⟩
  have hK₀ : (K₀ : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) = Metric.closedBall 0 1 := rfl
  rw [Measure.addHaarMeasure_unique (Measure.map e volume) K₀,
    Measure.addHaarMeasure_unique (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) K₀]
  congr 1
  rw [hK₀, Measure.map_apply e.continuous.measurable Metric.isClosed_closedBall.measurableSet]
  have h1 : e ⁻¹' Metric.closedBall 0 1 = Set.pi Set.univ fun _ : ι =>
      (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) ×ˢ
        Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) 1 := by
    ext y
    simp only [Set.mem_preimage, mem_closedBall_zero_iff, he, Set.mem_pi, Set.mem_univ,
      Set.mem_prod, true_and, forall_true_left, pi_norm_le_iff_of_nonneg zero_le_one, psi_apply]
    exact forall_comm
  have h2 : (Metric.closedBall 0 1 : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_closedBall_zero_iff, Set.mem_pi, Set.mem_univ, forall_true_left,
      pi_norm_le_iff_of_nonneg zero_le_one]
  have h3 : volume (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  rw [h1, h2, volume_pi_pi, volume_pi_pi]
  simp only [volume_pi_pi, Measure.volume_eq_prod, Measure.prod_prod, h3, one_mul]
  exact Finset.prod_comm

def piBasis : Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (ι → mixedSpace K) :=
  Pi.basis fun _ => latticeBasis K

theorem fundamentalDomain_piBasis : ZSpan.fundamentalDomain (piBasis K ι) =
    Set.pi Set.univ fun _ => ZSpan.fundamentalDomain (latticeBasis K) := by
  ext y
  simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies, forall_const, piBasis,
    Pi.basis_repr, Sigma.forall]

theorem mem_span_piBasis (y : ι → mixedSpace K) :
    y ∈ Submodule.span ℤ (Set.range (piBasis K ι)) ↔
      ∀ i, ∃ a : 𝓞 K, mixedEmbedding K (algebraMap (𝓞 K) K a) = y i := by
  simp only [Basis.mem_span_iff_repr_mem ℤ, piBasis, Pi.basis_repr, Sigma.forall]
  refine forall_congr' fun i => ?_
  refine (Basis.mem_span_iff_repr_mem ℤ (latticeBasis K) (y i)).symm.trans ?_
  rw [mem_span_latticeBasis]
  simp [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range]

theorem covolume_piBasis :
    ZLattice.covolume (Submodule.span ℤ (Set.range (piBasis K ι))) volume =
      ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (piBasis K ι) volume),
    measureReal_def, fundamentalDomain_piBasis, volume_pi_pi, ENNReal.toReal_prod, Finset.prod_const,
    Finset.card_univ, ← measureReal_def,
    ← ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (latticeBasis K) volume),
    span_latticeBasis, covolume_integerLattice]

end Formalism.HermitianLattices.Ext.L3.BallC
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MeasurableSetBallSet

section

@[expose] public section

open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise

open scoped Classical


set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallD

open BallB BallC

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def emb (b : Basis (Fin (finrank K V)) K V) : V →+ (Fin (finrank K V) → mixedSpace K) where
  toFun x := fun i => mixedEmbedding K (b.repr x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_apply (b : Basis (Fin (finrank K V)) K V) (x : V) (i : Fin (finrank K V)) :
    emb b x i = mixedEmbedding K (b.repr x i) := rfl

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_injective (b : Basis (Fin (finrank K V)) K V) : Function.Injective (emb b) := by
  intro x y hxy
  apply b.repr.injective
  ext i
  exact mixedEmbedding_injective K (congrFun hxy i)

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem psi_emb [IsEmpty {w : InfinitePlace K // w.IsReal}] (b : Basis (Fin (finrank K V)) K V)
    (x : V) (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin (finrank K V)) :
    psi K (Fin (finrank K V)) (emb b x) w i = w.1.embedding (b.repr x i) := by
  rw [psi_apply, emb_apply, mixedEmbedding_apply_isComplex]

def lat (b : Basis (Fin (finrank K V)) K V) (L : Submodule (𝓞 K) V) :
    Submodule ℤ (Fin (finrank K V) → mixedSpace K) :=
  AddSubgroup.toIntSubmodule (L.toAddSubgroup.map (emb b))

omit [StarRing K] [IsScalarTower (𝓞 K) K V] in
theorem mem_lat {b : Basis (Fin (finrank K V)) K V} {L : Submodule (𝓞 K) V}
    {y : Fin (finrank K V) → mixedSpace K} : y ∈ lat b L ↔ ∃ x ∈ L, emb b x = y := Iff.rfl

omit [StarRing K] in
theorem lat_span (b : Basis (Fin (finrank K V)) K V) :
    lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (piBasis K (Fin (finrank K V)))) := by
  ext y
  rw [mem_span_piBasis, mem_lat]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨a, ha⟩ := (b.mem_span_iff_repr_mem (𝓞 K) x).1 hx i
    exact ⟨a, by rw [ha]; rfl⟩
  · intro hy
    choose a ha using hy
    have hr : ∀ i, b.repr (b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i)) i =
        algebraMap (𝓞 K) K (a i) := by
      intro i
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    refine ⟨b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i),
      (b.mem_span_iff_repr_mem (𝓞 K) _).2 fun i => ⟨a i, (hr i).symm⟩, funext fun i => ?_⟩
    rw [emb_apply, hr, ha]

def ballSet [IsEmpty {w : InfinitePlace K // w.IsReal}] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (b : Basis (Fin (finrank K V)) K V) : Set (Fin (finrank K V) → mixedSpace K) :=
  (psi K (Fin (finrank K V))) ⁻¹' Set.pi Set.univ fun w =>
    ell fun i => (w.1.embedding (h (b i) (b i))).re

variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem measurableSet_ballSet : MeasurableSet (ballSet h b) :=
  ((isClosed_set_pi fun _ _ => isClosed_ell _).preimage
    (psi K (Fin (finrank K V))).toContinuousLinearEquiv.continuous).measurableSet

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem convex_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Convex ℝ (ballSet h b) :=
  (convex_pi fun w _ => convex_ell (hA w)).linear_preimage (psi K (Fin (finrank K V))).toLinearMap

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isBounded_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Bornology.IsBounded (ballSet h b) := by
  have h1 : ballSet h b = (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm ''
      Set.pi Set.univ fun w => ell fun i => (w.1.embedding (h (b i) (b i))).re :=
    ((psi K (Fin (finrank K V))).toContinuousLinearEquiv.image_symm_eq_preimage _).symm
  rw [h1]
  exact (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm.lipschitzWith.isBounded_image
    (Bornology.IsBounded.pi fun w => isBounded_ell (hA w))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem volume_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    volume.real (ballSet h b) =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ InfinitePlace.nrComplexPlaces K /
        ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have hm : MeasurableSet (Set.pi Set.univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      ell fun i => (w.1.embedding (h (b i) (b i))).re) :=
    (isClosed_set_pi fun _ _ => isClosed_ell _).measurableSet
  rw [measureReal_def, ballSet,
    (measurePreserving_psi K (Fin (finrank K V))).measure_preimage hm.nullMeasurableSet,
    volume_pi_pi, ENNReal.toReal_prod]
  have h1 : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (volume (ell fun i => (w.1.embedding (h (b i) (b i))).re)).toReal =
        Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ) /
          ∏ i, (w.1.embedding (h (b i) (b i))).re := by
    intro w
    rw [volume_ell (hA w), ENNReal.toReal_ofReal]
    exact div_nonneg (by positivity) (Finset.prod_nonneg fun i _ => (hA w i).le)
  simp only [h1]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

theorem card_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (L : Submodule (𝓞 K) V) {j : ℕ} (hj : 0 < j) :
    ballCount h L ((j : ℝ) ^ 2) =
      Nat.card ↑(ballSet h b ∩ (j : ℝ)⁻¹ • (lat b L : Set (Fin (finrank K V) → mixedSpace K))) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have key : ∀ x : V, (j : ℝ)⁻¹ • emb b x ∈ ballSet h b ↔
      ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ (j : ℝ) ^ 2 := by
    intro x
    rw [forall_embedding_iff hK b ho x]
    simp only [ballSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, mem_ell,
      map_smul]
    refine forall_congr' fun w => ?_
    have h1 : ∀ i, Complex.normSq (((j : ℝ)⁻¹ • psi K (Fin (finrank K V)) (emb b x)) w i) =
        ((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i)) := by
      intro i
      rw [Pi.smul_apply, Pi.smul_apply, psi_emb, Complex.real_smul, map_mul, Complex.normSq_ofReal]
      field_simp
    simp only [h1]
    have h2 : ∑ i, (w.1.embedding (h (b i) (b i))).re *
        (((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i))) =
        (∑ i, (w.1.embedding (h (b i) (b i))).re *
          Complex.normSq (w.1.embedding (b.repr x i))) / (j : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, div_le_one (by positivity)]
  unfold ballCount
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨(j : ℝ)⁻¹ • emb b x.1, (key x.1).2 x.2.2,
      Set.smul_mem_smul_set ⟨x.1, x.2.1, rfl⟩⟩) ⟨?_, ?_⟩)
  · intro x y hxy
    have h1 : (j : ℝ)⁻¹ • emb b x.1 = (j : ℝ)⁻¹ • emb b y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (emb_injective b (smul_right_injective _ (inv_ne_zero hj'.ne') h1))
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy2
    exact ⟨⟨x, hx, (key x).1 hy1⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.BallD
end
end
end
