module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsOrthogonalProjectionPolynomialCompactUnitaStatement
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Group.Units
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.DataHost
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFun

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory Matrix Formalism.REAL

variable {n : ℕ}

def polyAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {f | ∃ d, ⇑f ∈ polyV ε d}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using mul_mem ha hb⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, by simpa using add_mem (polyV_mono ε (le_max_left a b) ha) (polyV_mono ε (le_max_right a b) hb)⟩
  algebraMap_mem' := by
    intro c
    refine ⟨0, ?_⟩
    convert const_mem ε 0 c using 1
    funext k; simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := by
    rintro f ⟨a, ha⟩
    refine ⟨a, ?_⟩
    convert star_mem ha using 1
    funext k; rfl

theorem toMK_injective (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  have h1 : ((a : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((b : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := Units.ext h
  exact Subtype.ext (Subtype.ext h1)

theorem polyAlg_separatesPoints (ε : Fin n → Bool) : (polyAlg ε).SeparatesPoints := by
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy (toMK_injective ε h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push_neg at hc
    exact hne (Matrix.ext hc)
  refine ⟨_, ⟨⟨coord ε (i, j, true), continuous_coord ε _⟩, ⟨1, show coord ε (i, j, true) ∈ polyV ε 1 from coord_mem ε _⟩, rfl⟩, ?_⟩
  simpa [coord] using hij

theorem polyAlg_dense (ε : Fin n → Bool) : (polyAlg ε).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (polyAlg_separatesPoints ε)

theorem integrable_cont (ε : Fin n → Bool) (F : C(KG ε, ℂ)) : Integrable F (muK ε) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_integral_cont (ε : Fin n → Bool) :
    Continuous fun F : C(KG ε, ℂ) => ∫ k, F k ∂(muK ε) := by
  refine (LipschitzWith.of_dist_le_mul fun F G => ?_).continuous (K := 1)
  rw [dist_eq_norm, ← integral_sub (integrable_cont ε F) (integrable_cont ε G)]
  have h := norm_integral_le_of_norm_le_const (μ := muK ε) (C := ‖F - G‖)
    (Filter.Eventually.of_forall fun k => by
      simpa using ContinuousMap.norm_coe_le_norm (F - G) k)
  simpa [probReal_univ, dist_eq_norm] using h

theorem eq_zero_of_orth_poly : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  intro n ε h hc horth
  let H : C(KG ε, ℂ) := ⟨h, hc⟩
  let Φ : C(KG ε, ℂ) → ℂ := fun F => ∫ k, star (F k) * h k ∂(muK ε)
  have hΦ : Continuous Φ := by
    have : Continuous fun F : C(KG ε, ℂ) => star F * H := (continuous_star).mul continuous_const
    exact (continuous_integral_cont ε).comp this
  have hclosed : IsClosed {F : C(KG ε, ℂ) | Φ F = 0} := isClosed_eq hΦ continuous_const
  have hsub : ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {F | Φ F = 0} := by
    rintro F ⟨d, hd⟩
    exact horth d _ hd
  have hcl : closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) = Set.univ := by
    have := polyAlg_dense ε
    rw [← StarSubalgebra.topologicalClosure_coe, this]
    rfl
  have hH : Φ H = 0 := by
    have : H ∈ closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by rw [hcl]; trivial
    exact hclosed.closure_subset_iff.mpr hsub this

  have hint : ∫ k, (Complex.normSq (h k) : ℂ) ∂(muK ε) = 0 := by
    have e : (fun k => (Complex.normSq (h k) : ℂ)) = fun k => star (h k) * h k := by
      funext k; rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [e]; exact hH
  have hint' : ∫ k, Complex.normSq (h k) ∂(muK ε) = 0 := by
    rw [integral_complex_ofReal] at hint
    exact_mod_cast hint
  have hnn : 0 ≤ᵐ[muK ε] fun k => Complex.normSq (h k) := Filter.Eventually.of_forall fun k => Complex.normSq_nonneg _
  have hcn : Continuous fun k => Complex.normSq (h k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hint'
  have hz : (fun k => Complex.normSq (h k)) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hcn continuous_const).mp hae
  funext k
  have := congrFun hz k
  simpa using this

end GlobalTheory.KFourier

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFunStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier


theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_compactUnitaryPolyFun : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  first | exact @GlobalTheory.KFourier.eq_zero_of_orth_poly | exact GlobalTheory.KFourier.eq_zero_of_orth_poly | (intros; apply GlobalTheory.KFourier.eq_zero_of_orth_poly <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.PairingConvolutionSwap

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section
namespace GlobalTheory.KFourier

theorem pairing_convolution_swap {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ)
    (he : Continuous e) (hq : Continuous q) (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : (muK ε).IsInvInvariant := ⟨(compact_haar_holds n ε).2.2.2⟩
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))

  have h1 : ∀ k' : KG ε, ∫ k, e k * g (k' * k) ∂(muK ε) = ∫ y, e (k'⁻¹ * y) * g y ∂(muK ε) := by
    intro k'
    have := integral_mul_left_eq_self (μ := muK ε) (fun y => e (k'⁻¹ * y) * g y) k'
    rw [← this]; simp [← mul_assoc]

  have h2 : ∀ y : KG ε, ∫ k', star (q k') * e (k'⁻¹ * y) ∂(muK ε) =
      ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) := by
    intro y
    have a := integral_inv_eq_self (fun x => star (q (y * x)) * e ((y * x)⁻¹ * y)) (muK ε)
    have b := integral_mul_left_eq_self (μ := muK ε) (fun k' => star (q k') * e (k'⁻¹ * y)) y
    rw [← b, ← a]
    congr 1; funext x
    rw [mul_comm]; congr 2; group
  have hcont : Continuous (fun p : KG ε × KG ε => star (q p.1) * e (p.1⁻¹ * p.2) * g p.2) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (k' y : KG ε) => star (q k') * e (k'⁻¹ * y) * g y)
      ((muK ε).prod (muK ε)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε)
      = ∫ k', ∫ y, star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) := by
        congr 1; funext k'
        rw [h1, ← integral_const_mul]
        congr 1; funext y; ring
    _ = ∫ y, ∫ k', star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) :=
        integral_integral_swap hint
    _ = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
        congr 1; funext y
        rw [← h2, ← integral_const_mul]
        congr 1; funext k'; ring

end GlobalTheory.KFourier
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.PairingConvolutionSwapStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier


theorem _root_.GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap : ∀ {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ), Continuous e → Continuous q → Continuous g → ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.pairing_convolution_swap | exact GlobalTheory.KFourier.pairing_convolution_swap | (intros; apply GlobalTheory.KFourier.pairing_convolution_swap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory
variable {n : ℕ}

theorem orth_decomp_L (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ polyV ε d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 :=
  GlobalTheory.T.exists_orthogonal_projection_polynomial_compact_unitary ε d p hp

theorem conv_swap_L (ε : Fin n → Bool) (e q g : KG ε → ℂ) (he : Continuous e) (hq : Continuous q)
    (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) :=
  GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap ε e q g he hq hg

theorem eq_zero_of_orth_L (ε : Fin n → Bool) (h : KG ε → ℂ) (hh : Continuous h)
    (ho : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) : h = 0 :=
  GlobalTheory.T.eq_zero_of_orthogonal_compactUnitaryPolyFun ε h hh ho

theorem integrable_of_cont (ε : Fin n → Bool) {f : KG ε → ℂ} (hf : Continuous f) : Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem firstCountable_KG (ε : Fin n → Bool) : FirstCountableTopology (KG ε) :=
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  ((isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).isInducing.firstCountableTopology

theorem continuous_param (ε : Fin n → Bool) {F : KG ε → KG ε → ℂ} (hF : Continuous (Function.uncurry F)) :
    Continuous fun a => ∫ k, F a k ∂(muK ε) := by
  haveI := firstCountable_KG ε
  have := continuous_parametric_integral_of_continuous (μ := muK ε) hF (s := Set.univ) isCompact_univ
  simpa [Measure.restrict_univ] using this

theorem sum_ker_poly (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) :
    ∀ d, ∀ p ∈ polyV ε d, ∑ i ∈ Finset.range (d + 1), ∫ k, e i k * p k ∂(muK ε) = p 1 := by
  intro d
  induction d with
  | zero =>
    intro p hp
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    exact (he 0).2.2 p hp (fun q hq => by simp [lowV] at hq; simp [hq])
  | succ d ih =>
    intro p hp
    obtain ⟨p', hp', horth⟩ := orth_decomp_L ε d p (continuous_of_mem hp)
    have hp'' : (fun k => p k - p' k) ∈ polyV ε (d + 1) :=
      sub_mem hp (polyV_mono ε (Nat.le_succ d) hp')
    have hcp : Continuous p := continuous_of_mem hp
    have hcp' : Continuous p' := continuous_of_mem hp'
    have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
    have hsplit : ∀ i, ∫ k, e i k * p k ∂(muK ε) =
        ∫ k, e i k * p' k ∂(muK ε) + ∫ k, e i k * (p k - p' k) ∂(muK ε) := by
      intro i
      rw [← integral_add (integrable_of_cont ε (f := fun k => e i k * p' k) ((hce i).mul hcp'))
        (integrable_of_cont ε (f := fun k => e i k * (p k - p' k)) ((hce i).mul (hcp.sub hcp')))]
      congr 1; funext k; ring
    rw [Finset.sum_range_succ, hsplit (d + 1), Finset.sum_congr rfl (fun i _ => hsplit i),
      Finset.sum_add_distrib, ih p' hp']
    have h0 : ∫ k, e (d + 1) k * p' k ∂(muK ε) = 0 := (he (d + 1)).2.1 p' hp'
    have h1 : ∫ k, e (d + 1) k * (p k - p' k) ∂(muK ε) = p 1 - p' 1 :=
      (he (d + 1)).2.2 _ hp'' (fun q hq => horth q hq)
    have h2 : ∀ i ∈ Finset.range (d + 1), ∫ k, e i k * (p k - p' k) ∂(muK ε) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hs : (fun k => star (e i k)) ∈ polyV ε d := polyV_mono ε hi' (star_mem (he i).1)
      have := horth _ hs
      simpa using this
    rw [Finset.sum_eq_zero h2, h0, h1]
    ring

theorem ker_vanish (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) {d i : ℕ} (hi : d < i)
    {p : KG ε → ℂ} (hp : p ∈ polyV ε d) : ∫ k, e i k * p k ∂(muK ε) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact (he (j + 1)).2.1 p (polyV_mono ε (by omega) hp)

theorem hasSum_kFourier (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i))
    (g : KG ε → ℂ) (hg : Continuous g) (b : ℕ → ℝ) (hb : Summable b)
    (hbd : ∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) :
    HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
  set P : ℕ → KG ε → ℂ := fun i k' => ∫ k, e i k * g (k' * k) ∂(muK ε) with hPdef
  have hPc : ∀ i, Continuous (P i) := fun i =>
    continuous_param ε (F := fun k' k => e i k * g (k' * k))
      (((hce i).comp continuous_snd).mul (hg.comp (continuous_fst.mul continuous_snd)))
  have hsum : ∀ k', Summable (fun i => P i k') := fun k' => Summable.of_norm_bounded hb (fun i => hbd i k')
  set u : KG ε → ℂ := fun k' => ∑' i, P i k' with hudef
  have hu : Continuous u := continuous_tsum hPc hb hbd
  have key : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (u k - g k) ∂(muK ε) = 0 := by
    intro d q hq
    have hcq : Continuous q := continuous_of_mem hq
    obtain ⟨M, hM⟩ : ∃ M, ∀ k, ‖star (q k)‖ ≤ M := by
      obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_star.comp hcq)).isBounded.exists_norm_le
      exact ⟨M, fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    have hint : ∀ i, Integrable (fun k => star (q k) * P i k) (muK ε) := fun i =>
      integrable_of_cont ε ((continuous_star.comp hcq).mul (hPc i))
    have hnorm : ∀ i, ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ M * b i := by
      intro i
      calc ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ ∫ _k, M * b i ∂(muK ε) := by
            refine integral_mono (hint i).norm (integrable_const _) (fun k => ?_)
            rw [norm_mul]
            exact mul_le_mul (hM k) (hbd i k) (norm_nonneg _) ((norm_nonneg _).trans (hM k))
        _ = M * b i := by simp
    have hsn : Summable fun i => ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) :=
      Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) hnorm (hb.mul_left M)
    have e1 : ∫ k, star (q k) * u k ∂(muK ε) = ∑' i, ∫ k, star (q k) * P i k ∂(muK ε) := by
      rw [integral_tsum_of_summable_integral_norm hint hsn]
      congr 1; funext k
      rw [hudef]; simp only
      exact (tsum_mul_left).symm
    set r : ℕ → KG ε → ℂ := fun i y => ∫ x, e i x * star (q (y * x⁻¹)) ∂(muK ε) with hrdef
    have hpy : ∀ y, (fun x => star (q (y * x⁻¹))) ∈ polyV ε d := fun y =>
      star_mem (inv_mem (φ := fun k => q (y * k)) (mul_left_mem y hq))
    have hrc : ∀ i, Continuous (r i) := fun i =>
      continuous_param ε (F := fun y x => e i x * star (q (y * x⁻¹)))
        (((hce i).comp continuous_snd).mul (continuous_star.comp (hcq.comp (continuous_fst.mul continuous_snd.inv))))
    have e2 : ∀ i, ∫ k, star (q k) * P i k ∂(muK ε) = ∫ y, g y * r i y ∂(muK ε) := fun i =>
      conv_swap_L ε (e i) q g (hce i) hcq hg
    have hr0 : ∀ i ∉ Finset.range (d + 1), ∫ y, g y * r i y ∂(muK ε) = 0 := by
      intro i hi
      have hi' : d < i := by simpa using hi
      have : ∀ y, r i y = 0 := fun y => ker_vanish ε e he hi' (hpy y)
      simp [this]
    have hrs : ∀ y, ∑ i ∈ Finset.range (d + 1), r i y = star (q y) := by
      intro y
      have := sum_ker_poly ε e he d _ (hpy y)
      simp only [hrdef]
      simpa using this
    have e3 : ∫ k, star (q k) * u k ∂(muK ε) = ∫ k, star (q k) * g k ∂(muK ε) := by
      rw [e1, tsum_congr e2, tsum_eq_sum hr0, ← integral_finsetSum]
      · congr 1; funext y
        rw [← Finset.mul_sum, hrs y, mul_comm]
      · intro i _
        exact integrable_of_cont ε (hg.mul (hrc i))
    have hsub : (fun k => star (q k) * (u k - g k)) = fun k => star (q k) * u k - star (q k) * g k := by
      funext k; ring
    rw [hsub, integral_sub (integrable_of_cont ε (f := fun k => star (q k) * u k) ((continuous_star.comp hcq).mul hu))
      (integrable_of_cont ε (f := fun k => star (q k) * g k) ((continuous_star.comp hcq).mul hg)), e3, sub_self]
  have hzero := eq_zero_of_orth_L ε (fun k => u k - g k) (hu.sub hg) key
  have h1 : u 1 = g 1 := sub_eq_zero.1 (congrFun hzero 1)
  have h2 : u 1 = ∑' i, ∫ k, e i k * g k ∂(muK ε) := by simp [hudef, hPdef]
  rw [← h1, h2]
  have := (hsum 1).hasSum
  simpa [hPdef] using this

end GlobalTheory.KFourier
end
end
end
