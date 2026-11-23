module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierEqFiniteFourierSumDepth
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierInversionSchwartzBruhat

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

noncomputable section
namespace GlobalTheory.ColFourier

theorem fourier_pi_inversion_at {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type*} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} {c : kˣ} {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) (a : n → k) :
    ∫ y : n → k, (∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)
      ∂(Measure.pi fun _ => ν) = g a := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hh : (fun x => g (x + a)) ∈ SB (n → k) :=
    ⟨hg.1.comp_continuous (by fun_prop), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have h1 := (FourierPi.fourier_pi_of_conductor h hν hh).2
  simp only [zero_add] at h1
  rw [← h1]
  congr 1
  funext y
  rw [← integral_mul_const,
    ← integral_add_right_eq_self (fun x => g x * (ψ (x ⬝ᵥ y) : ℂ) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)) a]
  congr 1
  funext x
  rw [add_dotProduct, AddChar.map_add_eq_mul, AddChar.inv_apply', dotProduct_comm y a, mul_assoc,
    ← Circle.coe_mul, mul_inv_cancel_right]

theorem fourierInt_inv_fourierInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  have hν : IsSelfDual ψ m := isSelfDual_of_isUnitVol m hψ hm
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  funext X
  have h0 := comp_setCols_mem_SB hΞ P X
  have hg : (fun x : (_ : A) × P → k => Ξ (setCols P X (Matrix.of fun i j => x ⟨i, j⟩))) ∈
      SB ((_ : A) × P → k) :=
    ⟨h0.1.comp_continuous (f := fun x : (_ : A) × P → k => (Matrix.of fun i j => x ⟨i, j⟩ : Matrix A P k))
        (continuous_pi fun i => continuous_pi fun j => continuous_apply _),
      HasCompactSupport.intro (h0.2.image (f := fun (U : Matrix A P k) (p : (_ : A) × P) => U p.1 p.2)
        (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
        fun x hx => image_eq_zero_of_notMem_tsupport (f := fun U => Ξ (setCols P X U)) fun h => hx ⟨_, h, rfl⟩⟩
  have h1 := fourier_pi_inversion_at hψ hν hg (fun p => X p.1 p.2)
  have h2 : setCols P X (Matrix.of fun i (j : P) => X i j) = X := setCols_restrictCols P X
  simp only [h2] at h1
  rw [← h1, fourierInt_eq_pi]
  congr 1
  funext y
  rw [fourierInt_eq_pi]
  have h3 : (fun p : (_ : A) × P => setCols P X (Matrix.of fun i j => y ⟨i, j⟩) p.1 p.2) = y := by
    funext p
    simp [setCols, p.2.2]
  simp only [setCols_setCols, h3]

end GlobalTheory.ColFourier
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierInversionSchwartzBruhatStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

theorem _root_.GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  first | exact @GlobalTheory.ColFourier.fourierInt_inv_fourierInt | exact GlobalTheory.ColFourier.fourierInt_inv_fourierInt | (intros; apply GlobalTheory.ColFourier.fourierInt_inv_fourierInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierMemSchwartzBruhat

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A C : Type} [Fintype A] [DecidableEq C]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem setCols_eq_add_offBlock (P : Finset C) (Y Y' : Matrix A C k) (T : Matrix A P k) :
    setCols P Y' T = setCols P Y T + setCols P (Y' - Y) 0 := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem setCols_of_add (P : Finset C) (Y : Matrix A C k) (x t : (Σ _ : A, P) → k) :
    setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩) =
      setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) + setCols P 0 (Matrix.of fun i j => t ⟨i, j⟩) := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_left (P : Finset C) (T : Matrix A P k) :
    Continuous fun Y : Matrix A C k => setCols P Y T := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]; exact continuous_const
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_id.matrix_elem i j

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × ((Σ _ : A, P) → k) =>
      setCols P q.1 (Matrix.of fun i j => q.2 ⟨i, j⟩) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨i, ⟨j, h⟩⟩ : (Σ _ : A, P))).comp continuous_snd
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_fst.matrix_elem i j

omit [DecidableEq C] in
theorem continuous_pairCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × Matrix A P k => pairCols P q.1 q.2 := by
  unfold pairCols
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_snd.matrix_elem i j).mul (continuous_fst.matrix_elem i (j : C))

end GlobalTheory.ColFourier

theorem GlobalTheory.ColFourier.fourierInt_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ m P Ξ ∈ SB (Matrix A C k) := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have hinv := GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant hΞ
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun Y => ?_, ?_⟩
  · have hK : IsCompact (restrictCols P '' tsupport Ξ) := hΞ.2.image (continuous_restrictCols P)
    have h1 : ∀ᶠ Y' in 𝓝 Y, ∀ X, Ξ (X + setCols P (Y' - Y) 0) = Ξ X := by
      have hc : Continuous (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) :=
        (continuous_setCols_left P 0).comp (continuous_id.sub continuous_const)
      have h0 : setCols P (Y - Y) (0 : Matrix A P k) = 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have ht : Filter.Tendsto (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) (𝓝 Y) (𝓝 0) := by
        convert hc.tendsto Y using 2
        exact h0.symm
      exact ht.eventually hinv
    have h2 : ∀ᶠ Y' in 𝓝 Y, ∀ T ∈ restrictCols P '' tsupport Ξ,
        ψ (pairCols P Y' T) = ψ (pairCols P Y T) := by
      refine hK.eventually_forall_of_forall_eventually fun T _ => ?_
      have h3 : IsLocallyConstant fun q : Matrix A C k × Matrix A P k =>
          (ψ (pairCols P q.1 q.2), ψ (pairCols P Y q.2)) :=
        (hψ.isLocallyConstant.comp_continuous (continuous_pairCols_pair P)).prodMk
          (hψ.isLocallyConstant.comp_continuous
            ((continuous_pairCols_pair P).comp (continuous_const.prodMk continuous_snd)))
      filter_upwards [h3.eventually_eq (Y, T)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1, h2] with Y' hY1 hY2
    unfold fourierInt
    congr 1
    funext T
    rw [setCols_eq_add_offBlock P Y Y' T, hY1]
    by_cases hT : setCols P Y T ∈ tsupport Ξ
    · rw [hY2 T ⟨_, hT, restrictCols_setCols P Y T⟩]
    · simp [image_eq_zero_of_notMem_tsupport hT]
  · have hc : Continuous fun t : (Σ _ : A, P) → k =>
        setCols P (0 : Matrix A C k) (Matrix.of fun i j => t ⟨i, j⟩) :=
      (continuous_setCols_pair P).comp (continuous_const.prodMk continuous_id)
    have h0 : setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩) = 0 := by
      ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
    have hU : {Z : Matrix A C k | ∀ X, Ξ (X + Z) = Ξ X} ∈
        𝓝 (setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩)) := by
      rw [h0]; exact hinv
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (hc.continuousAt.preimage_mem_nhds hU)
    refine HasCompactSupport.intro ((hΞ.2.prod (FourierPi.isCompact_box (1 * s⁻¹))).image
      (continuous_setCols_pair P)) fun Y hY => ?_
    rw [fourierInt_eq_pi]
    by_cases hy : (fun p : (Σ _ : A, P) => Y p.1 p.2) ∈ FourierPi.box (Σ _ : A, P) (1 * s⁻¹)
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      have hback : setCols P (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
          (Matrix.of fun i j => (fun p : (Σ _ : A, P) => Y p.1 p.2) ⟨i, j⟩) = Y := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have hX : setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) ∉ tsupport Ξ := fun hX =>
        hY ⟨(_, fun p => Y p.1 p.2), ⟨hX, hy⟩, hback⟩
      simp [image_eq_zero_of_notMem_tsupport hX]
    · refine FourierPi.fourier_eq_zero_pi (Measure.pi fun _ : (Σ _ : A, P) => m) hψ (s := s)
        (f := fun x => Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))) (fun t ht x => ?_) hy
      show Ξ (setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩)) = Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
      rw [setCols_of_add]
      exact hs ht _
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierMemSchwartzBruhatStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

theorem _root_.GlobalTheory.T.partialColumnFourier_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ m P Ξ ∈ SB (Matrix A C k) := by
  first | exact @GlobalTheory.ColFourier.fourierInt_mem_SB | exact GlobalTheory.ColFourier.fourierInt_mem_SB | (intros; apply GlobalTheory.ColFourier.fourierInt_mem_SB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPartialFourierColumnBlockSchwartzBruhat

section

@[expose] public section

namespace GlobalTheory.ColFourier
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem fourierInt_add (ψ : AddChar k Circle) (m : Measure k) (hψ : HasConductor ψ 1) (hm : IsUnitVol m)
    (P : Finset C) {Ξ₁ Ξ₂ : Matrix A C k → ℂ} (h₁ : Ξ₁ ∈ SB (Matrix A C k)) (h₂ : Ξ₂ ∈ SB (Matrix A C k)) :
    fourierInt ψ m P (Ξ₁ + Ξ₂) = fourierInt ψ m P Ξ₁ + fourierInt ψ m P Ξ₂ := by
  haveI := hm.1
  haveI := secondCountable k
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : BorelSpace (Matrix A P k) := inferInstanceAs (BorelSpace (A → P → k))
  have hi : ∀ Ξ ∈ SB (Matrix A C k), ∀ Y : Matrix A C k,
      Integrable (fun U => Ξ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ)) (volM m A P) := by
    intro Ξ hΞ Y
    have hg := comp_setCols_mem_SB hΞ P Y
    have hc : Continuous fun U : Matrix A P k => pairCols P Y U := by unfold pairCols; fun_prop
    exact (hg.1.continuous.integrable_of_hasCompactSupport hg.2).mul_bdd (c := 1)
      ((continuous_subtype_val.comp (hψ.continuous.comp hc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun U => (Circle.norm_coe _).le)
  funext Y
  simp only [fourierInt, Pi.add_apply, add_mul]
  exact integral_add (hi _ h₁ Y) (hi _ h₂ Y)

theorem fourierInt_shift [Fintype C] (ψ : AddChar k Circle) (m : Measure k) (hm : IsUnitVol m) (P : Finset C)
    (Ξ : Matrix A C k → ℂ) (T R : Matrix A C k) (hT : ∀ r, ∀ s ∉ P, T r s = 0) (hR : ∀ r, ∀ s ∈ P, R r s = 0) :
    fourierInt ψ m P (fun S => (ψ (GlobalTheory.FlipMatch.pairM S R) : ℂ) * Ξ (S + T)) =
      fun Z => (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) * fourierInt ψ m P Ξ Z := by
  haveI := hm.1
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : MeasurableAdd (Matrix A P k) := inferInstanceAs (MeasurableAdd (A → P → k))
  funext Z
  unfold fourierInt
  set Tp := restrictCols P T
  rw [← integral_add_right_eq_self (μ := volM m A P)
    (fun U => Ξ (setCols P Z U) * (ψ (pairCols P Z U) : ℂ)) Tp, ← integral_const_mul]
  congr 1
  funext U
  have ea : GlobalTheory.FlipMatch.pairM (setCols P Z U) R = GlobalTheory.FlipMatch.pairM Z R := by
    simp only [GlobalTheory.FlipMatch.pairM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ∈ P
    · simp [setCols, h, hR i j h]
    · simp [setCols, h]
  have eb : setCols P Z U + T = setCols P Z (U + Tp) := by
    ext i j
    by_cases h : j ∈ P
    · simp [setCols, h, Tp, restrictCols]
    · simp [setCols, h, hT i j h]
  have ec : pairCols P Z (U + Tp) = pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T := by
    simp only [pairCols, GlobalTheory.FlipMatch.pairM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [hT i j hj]),
      ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Tp, restrictCols]
    ring
  have key : (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) *
      ψ (pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T) = ψ (GlobalTheory.FlipMatch.pairM Z R) * ψ (pairCols P Z U) := by
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2; ring
  dsimp only
  rw [ea, eb, ec]
  linear_combination (Ξ (setCols P Z (U + Tp))) * key.symm

end GlobalTheory.ColFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

theorem GlobalTheory.ColFourier.exists_blockFourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ P hϖ hψ
  borelize k
  obtain ⟨m, hm⟩ := exists_isUnitVol k
  haveI := hm.1
  have hψ' : HasConductor ψ⁻¹ 1 := GlobalTheory.ColFourier.hasConductor_inv hψ
  have hSB := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_mem_schwartzBruhat k A C χ m hχ hm P Ξ h
  have hInv := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat k A C χ m hχ hm P Ξ h
  let L : SB (Matrix A C k) →ₗ[ℂ] (Matrix A C k → ℂ) :=
    { toFun := fun Ξ => fourierInt ψ m P Ξ
      map_add' := fun a b => GlobalTheory.ColFourier.fourierInt_add ψ m hψ hm P a.2 b.2
      map_smul' := fun c a => by
        funext Y
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, fourierInt]
        rw [← integral_const_mul]
        congr 1; funext U; ring }
  obtain ⟨F, hF⟩ := LinearMap.exists_extend L
  have hFe : ∀ Ξ ∈ SB (Matrix A C k), F Ξ = fourierInt ψ m P Ξ := fun Ξ h => LinearMap.congr_fun hF ⟨Ξ, h⟩
  have hmod : ∀ Ξ ∈ SB (Matrix A C k), ∀ T R : Matrix A C k,
      (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) ∈ SB (Matrix A C k) := by
    intro Ξ hΞ T R
    have hc : Continuous fun S : Matrix A C k => pairM S R := by unfold pairM; fun_prop
    refine ⟨((hψ.isLocallyConstant.comp_continuous hc).comp (fun z : Circle => (z : ℂ))).mul
      (hΞ.1.comp_continuous (continuous_add_const T)), ?_⟩
    exact (hΞ.2.comp_homeomorph (Homeomorph.addRight T)).mul_left
  refine ⟨F, ⟨fun Ξ h => ?_, fun Ξ₁ h₁ Ξ₂ h₂ he => ?_, fun Ψ hΨ => ?_⟩, fun Ξ hΞ T R hT hR => ?_,
    fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ n hn => ?_⟩
  · show F Ξ ∈ SB (Matrix A C k)
    rw [hFe Ξ h]; exact hSB ψ hψ Ξ h
  · rw [hFe _ h₁, hFe _ h₂] at he
    rw [← hInv ψ hψ Ξ₁ h₁, ← hInv ψ hψ Ξ₂ h₂, he]
  · have h1 := hSB ψ⁻¹ hψ' Ψ hΨ
    refine ⟨_, h1, ?_⟩
    rw [hFe _ h1]
    simpa only [inv_inv] using hInv ψ⁻¹ hψ' Ψ hΨ
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    funext Z
    unfold fourierInt
    congr 1
    funext U
    have e1 : setCols P Z U + T = setCols P (Z + (T + R)) U := by
      ext i j
      by_cases h : j ∈ P
      · simp [setCols, h, hT i j h]
      · simp [setCols, h, hR i j h]
    have e2 : pairM (setCols P Z U) R + pairCols P Z U = pairCols P (Z + (T + R)) U := by
      simp only [pairM, pairCols, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [setCols, hj, hR i j hj]),
        ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [setCols, j.2, hT i j j.2]
      ring
    dsimp only
    rw [e1, ← e2, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    exact GlobalTheory.ColFourier.fourierInt_shift ψ m hm P Ξ T R hT hR
  · rw [hFe _ hΞ] at hn ⊢
    rw [← GlobalTheory.ColFourier.fourierInt_eq_fourierSum k A C ψ⁻¹ m ϖ hϖ hψ' hm P n _ hn]
    exact hInv ψ hψ Ξ hΞ
end
end
