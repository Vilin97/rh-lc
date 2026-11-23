module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.Assemble
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SimpBdM
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.Unfold

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.DiscrHolds

section

@[expose] public section

noncomputable section

open NumberField Matrix UpperTheory.V.KT

namespace PositivityTheory.KB.LocalOverlapAverage

theorem discr_holds : Discr := by
  unfold Discr
  intro L _ _ N K hK
  have hc : Continuous (fun γ : Sp L N => fun (w : InfinitePlace L) (i j : Fin N) =>
      ((γ w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) := by
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  set S : Set (𝓞 L) := {x | ∀ w : InfinitePlace L, ‖w.embedding (x : L)‖ ≤ C} with hS
  have hSfin : S.Finite := by
    have h0 := Embeddings.finite_of_norm_le L ℂ C
    refine (h0.preimage (Set.injOn_of_injective (f := fun x : 𝓞 L => (x : L))
      RingOfIntegers.coe_injective)).subset ?_
    intro x hx
    refine ⟨RingOfIntegers.isIntegral_coe x, fun φ => ?_⟩
    have h1 := hx (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1
  have hT : (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hSfin
  have hU : {A : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) |
      (A : Matrix (Fin N) (Fin N) (𝓞 L)) ∈ Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S}.Finite :=
    hT.preimage (Set.injOn_of_injective Subtype.val_injective)
  refine (hU.image (MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w))).subset ?_
  rintro γ ⟨⟨A, rfl⟩, hγK⟩
  refine ⟨A, ?_, rfl⟩
  intro i _ j _ w
  have h2 := hC _ hγK
  have h3 : ‖(fun (w : InfinitePlace L) (i j : Fin N) =>
      ((((MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w)) A) w :
        Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) w i j‖ ≤ C :=
    (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans ((norm_le_pi_norm _ w).trans h2))
  exact h3

end PositivityTheory.KB.LocalOverlapAverage

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.MargInt

section

@[expose] public section

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.LocalOverlapAverage

def Yb (H : Type) : Type := H × Bool

instance (H : Type) [Group H] : MulAction H (Yb H) where
  smul h p := ((h * p.1 : H), p.2)
  one_smul p := by
    change ((1 * p.1 : H), p.2) = p
    rw [one_mul]
    rfl
  mul_smul g h p := by
    change ((g * h * p.1 : H), p.2) = ((g * (h * p.1) : H), p.2)
    rw [mul_assoc]

theorem marg {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin (n + 1)) (f : (Fin n → X) → ℝ) :
    ∫ x, f (fun j => x (i.succAbove j)) ∂(Measure.pi fun _ : Fin (n + 1) => P) =
      ∫ x, f x ∂(Measure.pi fun _ : Fin n => P) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i).integral_comp'
    (fun p : X × (Fin n → X) => f p.2)
  rw [integral_fun_snd] at h
  simp only [probReal_univ, one_smul] at h
  exact h

theorem marg_int {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin (n + 1)) (f : (Fin n → X) → ℝ) (hf : Integrable f (Measure.pi fun _ : Fin n => P)) :
    Integrable (fun x => f (fun j => x (i.succAbove j))) (Measure.pi fun _ : Fin (n + 1) => P) := by
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i
  have hφ : Measurable fun x : Fin (n + 1) → X => fun j => x (i.succAbove j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  have hmap : Measure.map (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j))
      (Measure.pi fun _ : Fin (n + 1) => P) = Measure.pi fun _ : Fin n => P := by
    have hcomp : (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j))
        = Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) i) := by
      funext x
      rfl
    rw [hcomp, ← Measure.map_map measurable_snd he.measurable, he.map_eq, Measure.map_snd_prod,
      measure_univ, one_smul]
  rw [← hmap] at hf
  exact hf.comp_measurable hφ

theorem avgS_of (hEv : SEv) : AvgS := by
  intro G H Y X _ _ _ _ ρ k F P _ e y₀ hinv hcoc hint z hz
  let F' : (Fin (k + 2) → Yb H) → ℝ := fun p =>
    ∫ x, F (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀)) ∂(Measure.pi fun _ => P)
  have hInv' : Inv ρ F' := by
    intro g p
    change ∫ x, F (fun j => (ρ g * (p j).1) • (if (p j).2 = true then e (x j) else y₀))
        ∂(Measure.pi fun _ => P) = F' p
    simp only [mul_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact hinv g (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀))
  have hcoc' : dC F' = 0 := by
    funext p
    let Q : (Fin (k + 3) → X) → Fin (k + 3) → Y := fun x j =>
      (p j).1 • (if (p j).2 = true then e (x j) else y₀)
    have hint' : ∀ i : Fin (k + 3),
        Integrable (fun x => F (fun j => Q x (i.succAbove j))) (Measure.pi fun _ => P) := by
      intro i
      exact marg_int P i _ (hint (fun j => (p (i.succAbove j)).1) (fun j => (p (i.succAbove j)).2))
    have hterm : ∀ i : Fin (k + 3), F' (fun j => p (i.succAbove j))
        = ∫ x, F (fun j => Q x (i.succAbove j)) ∂(Measure.pi fun _ => P) :=
      fun i => (marg P i _).symm
    change ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F' (fun j => p (i.succAbove j)) = 0
    calc ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F' (fun j => p (i.succAbove j))
        = ∑ i : Fin (k + 3), ∫ x, (-1 : ℝ) ^ (i : ℕ) * F (fun j => Q x (i.succAbove j))
            ∂(Measure.pi fun _ => P) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hterm i, integral_const_mul]
      _ = ∫ x, ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F (fun j => Q x (i.succAbove j))
            ∂(Measure.pi fun _ => P) :=
          (integral_finsetSum _ fun i _ => (hint' i).const_mul _).symm
      _ = ∫ x, dC F (Q x) ∂(Measure.pi fun _ => P) := rfl
      _ = 0 := by simp [hcoc]
  let b₀ : Yb H := ((1 : H), false)
  let b₁ : Yb H := ((1 : H), true)
  have key1 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₀) = F (fun j => q j • y₀) := by
    intro q
    change ∫ x, F (fun j => (q j * 1) • (if false = true then e (x j) else y₀))
      ∂(Measure.pi fun _ => P) = _
    simp
  have key2 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₁)
      = ∫ x, F (fun j => q j • e (x j)) ∂(Measure.pi fun _ => P) := by
    intro q
    change ∫ x, F (fun j => (q j * 1) • (if true = true then e (x j) else y₀))
      ∂(Measure.pi fun _ => P) = _
    simp
  have h := (hEv G H (Yb H) ρ k F' hInv' hcoc').2 b₀ b₁ z hz
  simp only [ev, key1, key2] at h
  simpa [ev] using h

end PositivityTheory.KB.LocalOverlapAverage

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.Overlap

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.KB.LocalOverlapAverage

theorem overlapG_holds : OverlapG := by
  intro G _ _ _ _ _ _ Γ _ μ _ D hD hfin K hK
  have hT : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hF := hfin (K * K⁻¹) hT
  refine ⟨hF.toFinset.card, ?_⟩
  intro f hf hinv
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsum : ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    calc ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
        = ∑' γ : Γ, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) := by
          refine tsum_congr fun γ => ?_
          by_cases h : (γ : G) ∈ K * K⁻¹
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (γ : G) ∈ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from ⟨γ.2, h⟩)]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (γ : G) ∉ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from fun h' => h h'.2)]
      _ ≤ ∑' g : G, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g :=
          (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
      _ = ∑ g ∈ hF.toFinset, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g := by
          refine tsum_eq_sum fun g hg => ?_
          rw [Set.Finite.mem_toFinset] at hg
          exact Set.indicator_of_notMem hg _
      _ ≤ ∑ _g ∈ hF.toFinset, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun g _ => ?_
          unfold Set.indicator
          split_ifs <;> simp
      _ = (hF.toFinset.card : ℝ≥0∞) := by simp
  have hcount : ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    intro x
    by_cases hS : ∃ γ₀ : Γ, γ₀ • x ∈ K
    · obtain ⟨γ₀, h₀⟩ := hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
          ≤ ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) ((γ * γ₀⁻¹ : Γ) : G) := by
            refine ENNReal.tsum_le_tsum fun γ => ?_
            by_cases hγ : γ • x ∈ K
            · have hmem : ((γ * γ₀⁻¹ : Γ) : G) ∈ K * K⁻¹ := by
                refine ⟨γ • x, hγ, (γ₀ • x)⁻¹, by rw [Set.mem_inv, inv_inv]; exact h₀, ?_⟩
                simp [Subgroup.smul_def, mul_assoc]
              rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hmem]
            · rw [Set.indicator_of_notMem hγ]
              simp
        _ = ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) :=
            (Equiv.mulRight γ₀⁻¹).tsum_eq (fun γ : Γ => (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G))
        _ ≤ _ := hsum
    · push_neg at hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) = ∑' _γ : Γ, (0 : ℝ≥0∞) :=
            tsum_congr fun γ => Set.indicator_of_notMem (hS γ) _
        _ ≤ _ := by simp
  have hpt : ∀ γ : Γ, ∀ x : G, K.indicator f (γ • x)
      = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x := by
    intro γ x
    by_cases hx : γ • x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      simpa [Subgroup.smul_def] using hinv γ γ.2 x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hmeas : ∀ γ : Γ, Measurable fun x : G => K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x :=
    fun γ => ((measurable_const.indicator hKm).comp (measurable_const_smul γ)).mul hf
  calc ∫⁻ x in K, f x ∂μ = ∑' γ : Γ, ∫⁻ x in D, K.indicator f (γ • x) ∂μ := by
        rw [← lintegral_indicator hKm]
        exact hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ := by
        simp_rw [hpt]
    _ = ∫⁻ x in D, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) * f x ∂μ := by
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ x in D, (hF.toFinset.card : ℝ≥0∞) * f x ∂μ :=
        lintegral_mono fun x => by gcongr; exact hcount x
    _ = (hF.toFinset.card : ℝ≥0∞) * ∫⁻ x in D, f x ∂μ := lintegral_const_mul _ hf

end PositivityTheory.KB.LocalOverlapAverage

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SimpBd

section

@[expose] public section

namespace PositivityTheory.KB.LocalOverlapAverage

theorem simpBd_holds : SimpBd := by
  intro V _ _ _ _ _ μ _ q A B hB
  exact SimpM.main μ q A B hB

end PositivityTheory.KB.LocalOverlapAverage
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SLocOf

section

@[expose] public section

namespace PositivityTheory.KB

theorem sLoc_of (hEv : SEv) : SLoc :=
  LocalOverlapAverage.sLoc_of_parts (LocalOverlapAverage.avgS_of hEv) LocalOverlapAverage.simpBd_holds LocalOverlapAverage.unfold_holds
    LocalOverlapAverage.discr_holds LocalOverlapAverage.overlapG_holds

end PositivityTheory.KB
end
end
