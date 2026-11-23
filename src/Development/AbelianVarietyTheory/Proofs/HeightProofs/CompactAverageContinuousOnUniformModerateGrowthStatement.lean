module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AvgDerFamGrowth
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DerFamExpandWordsStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpSecondKindCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExpStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.AvgDerFamGrowthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.avg_derFam_growth_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  first | exact @GlobalTheory.KAvgDeriv.avg_derFam_growth | exact GlobalTheory.KAvgDeriv.avg_derFam_growth | (intros; apply GlobalTheory.KAvgDeriv.avg_derFam_growth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnAvgRightTranslates

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.AvgCont

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  refine isClosed_eq ?_ continuous_const
  exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id

theorem mul_mem_UJset_of_inUJ {n : ℕ} {ε : Fin n → Bool} {y m : Matrix (Fin n) (Fin n) ℂ}
    (hy : y ∈ UJset ε) (hm : Formalism.REAL.inUJ ε m) : y * m ∈ UJset ε := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have hm' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hm
  show (y * m)ᴴ * Formalism.REAL.Jm ε * (y * m) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc mᴴ * yᴴ * Formalism.REAL.Jm ε * (y * m) = mᴴ * (yᴴ * Formalism.REAL.Jm ε * y) * m := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hy', hm']

theorem continuous_maximalCompactSubgroup_toMatrix {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuousOn_avg_right_translates : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ),
    ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  intro n ε f hf e he
  rw [continuousOn_iff_continuous_restrict]
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (UJset ε) :=
    (isClosed_UJset ε).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let F : UJset ε → Formalism.REAL.KG ε → ℂ := fun y k => e k * f ((y : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK k)
  have hF : Continuous (Function.uncurry F) := by
    refine (he.comp continuous_snd).mul ?_
    have hmaps : ∀ p : UJset ε × Formalism.REAL.KG ε,
        (p.1 : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK p.2 ∈ UJset ε :=
      fun p => mul_mem_UJset_of_inUJ p.1.2 ((p.2 : Formalism.REAL.UJ ε).2)
    exact hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).matrix_mul
        ((continuous_maximalCompactSubgroup_toMatrix ε).comp continuous_snd)) hmaps
  have h := continuous_parametric_integral_of_continuous (μ := Formalism.REAL.muK ε) hF isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

end GlobalTheory.AvgCont
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnAvgRightTranslatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  first | exact @GlobalTheory.AvgCont.continuousOn_avg_right_translates | exact GlobalTheory.AvgCont.continuousOn_avg_right_translates | (intros; apply GlobalTheory.AvgCont.continuousOn_avg_right_translates <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableDerFamComp

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem measurable_derFam_comp (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ)
    (hF : GlobalTheory.TypeSum.IsDerFam ε F) (h0 : ContinuousOn (F []) (UJset ε)) :
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  intro l
  induction l with
  | nil =>
    intro _ T _ _ _ φ hφ hφU
    exact (h0.comp_continuous hφ hφU).measurable
  | cons X l ih =>
    intro hl T _ _ _ φ hφ hφU
    have hX : X ∈ lieSet ε := hl X (List.mem_cons_self ..)
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)

    let q : ℕ → T → ℂ := fun m t =>
      (((m : ℝ) + 1)⁻¹)⁻¹ • (F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X)) - F l (φ t))
    have hq : ∀ m, Measurable (q m) := by
      intro m
      have h1 : Measurable (fun t => F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))) :=
        ih hl' T (fun t => φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))
          (hφ.mul continuous_const) (fun t => mul_mem_UJ (hφU t) (exp_mem_UJ hX _))
      have h2 : Measurable (fun t => F l (φ t)) := ih hl' T φ hφ hφU
      exact (h1.sub h2).const_smul ((((m : ℝ) + 1)⁻¹)⁻¹ : ℝ)
    have hlim : ∀ t, Tendsto (fun m => q m t) atTop (𝓝 (F (X :: l) (φ t))) := by
      intro t
      have hd := hF l hl' X hX (φ t) (hφU t)
      have hs := hd.tendsto_slope_zero
      have hseq : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
        · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity
      have := hs.comp hseq
      refine this.congr fun m => ?_
      simp [q, Function.comp, zero_add]
    exact measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 hlim)

end GlobalTheory.TypeSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableDerFamCompStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ContinuousOn (F []) (UJset ε) → ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  first | exact @GlobalTheory.TypeSum.measurable_derFam_comp | exact GlobalTheory.TypeSum.measurable_derFam_comp | (intros; apply GlobalTheory.TypeSum.measurable_derFam_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageContinuousOnUniformModerateGrowth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.KAvgGrowth

theorem continuousOn_and_umg_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  classical
  intro n ε f hf hU e he
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  refine ⟨GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK n ε f hf e he, ?_⟩
  let B := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  let b : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n := fun i => (B i : Mx n)
  have hb : ∀ i, b i ∈ lieSet ε := fun i => by rw [lieSet_eq_lie]; exact (B i).2
  let c : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n → ℝ := fun i Z =>
    if h : Z ∈ lieSet ε then B.repr ⟨Z, by rwa [lieSet_eq_lie] at h⟩ i else 0
  have hsum : ∀ Z ∈ lieSet ε, Z = ∑ i, c i Z • b i := by
    intro Z hZ
    have hZ' : Z ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := by rwa [lieSet_eq_lie] at hZ
    have := congrArg Subtype.val (B.sum_repr ⟨Z, hZ'⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    simp only [c, dif_pos hZ]
    exact this.symm
  have hli : LinearIndependent ℝ b :=
    B.linearIndependent.map' (GlobalTheory.LowTypeDetermined.lie (Jm ε)).subtype (Submodule.ker_subtype _)
  have hC : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g := by
    intro l hl Z hZ g hg
    obtain ⟨τ, hτ0, hτ, hev⟩ := GlobalTheory.T.exp_second_kind_coordinates n ε _ b hb hli (fun Z hZ => ⟨fun i => c i Z, hsum Z hZ⟩) (fun i => c i Z)
    have h2 := GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero n ε N F hFd hFg l hl _ b hb g hg
    rw [← hτ0] at h2
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hτ
    have h4 : HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) (F (Z :: l) g) 0 := hFd l hl Z hZ g hg
    have h5 : (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) =ᶠ[nhds 0]
        ((fun t : Fin _ → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod)) ∘ τ) := by
      filter_upwards [hev] with t ht
      rw [← hsum Z hZ] at ht
      simp only [Function.comp_apply, ht]
    have h6 := h4.unique (h3.congr_of_eventuallyEq h5)
    rw [h6]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Complex.real_smul]
  have hD := GlobalTheory.T.derFam_ofFn_eq_sum_prod_coeff_of_expand n ε F hFd _ b c hb hC
  have hK : ∀ k : ↥(KG ε), toMK k ∈ UJset ε := fun k => K_le_UJ (toMK_mem_K k)
  have had : ∀ (k : ↥(KG ε)) (X : Mx n), X ∈ lieSet ε → (toMK k)⁻¹ * X * toMK k ∈ lieSet ε := by
    intro k X hX
    rw [lieSet_eq_lie] at hX ⊢
    exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (hK k) hX
  have hinvc : Continuous fun k : ↥(KG ε) => (toMK k)⁻¹ := by
    have e1 : (fun k : ↥(KG ε) => (toMK k)⁻¹) = fun k => toMK k⁻¹ := by
      funext k
      exact (Matrix.coe_units_inv _).symm
    rw [e1]
    exact (continuous_toMK ε).comp continuous_inv
  have hcc : ∀ i (X : Mx n), X ∈ lieSet ε → Continuous fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k) := by
    intro i X hX
    have hX' : ∀ k : ↥(KG ε), (toMK k)⁻¹ * X * toMK k ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := fun k => by
      have := had k X hX; rwa [lieSet_eq_lie] at this
    have e1 : (fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k)) =
        fun k => B.repr ⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ i := by
      funext k
      simp only [c, dif_pos (had k X hX)]
    rw [e1]
    have hm : Continuous fun k : ↥(KG ε) => (⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ : GlobalTheory.LowTypeDetermined.lie (Jm ε)) :=
      ((hinvc.matrix_mul continuous_const).matrix_mul (continuous_toMK ε)).subtype_mk _
    exact ((B.coord i).continuous_of_finiteDimensional).comp hm
  have e1 : ∀ (l : List (Mx n)) (k : ↥(KG ε)), (l.map fun X => (toMK k)⁻¹ * X * toMK k) =
      List.ofFn fun j => (toMK k)⁻¹ * l.get j * toMK k := by
    intro l k
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]; rfl
  have hbw : ∀ {m : ℕ} (J : Fin m → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε)))),
      ∀ Y ∈ List.ofFn (fun j => b (J j)), Y ∈ lieSet ε := by
    intro m J Y hY
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hY
    exact hb _
  have hUb : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (toMK k)⁻¹ * X * toMK k) g‖ ≤ C * (1 + hs g) ^ N := by
    intro l hl
    have hcb : ∀ i (j : Fin l.length), ∃ M : ℝ, ∀ k : ↥(KG ε), |c i ((toMK k)⁻¹ * l.get j * toMK k)| ≤ M := by
      intro i j
      obtain ⟨M, hM⟩ := (isCompact_univ.image (hcc i _ (hl _ (List.get_mem l j)))).isBounded.exists_norm_le
      exact ⟨M, fun k => by simpa [Real.norm_eq_abs] using hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    choose M hM using hcb
    have hCJ : ∀ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), ∃ C : ℝ,
        ∀ g ∈ UJset ε, ‖F (List.ofFn fun j => b (J j)) g‖ ≤ C * (1 + hs g) ^ N := fun J => hFg _ (hbw J)
    choose CJ hCJ using hCJ
    refine ⟨∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
      (∏ j, |M (J j) j|) * |CJ J|, fun k g hg => ?_⟩
    rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) g hg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)
    rw [norm_mul, norm_prod, mul_assoc]
    have hw : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
    refine mul_le_mul (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_) ?_ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => abs_nonneg _)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hM _ _ k).trans (le_abs_self _)
    · exact (hCJ J g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)
  have hF0c : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hMs : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      AEStronglyMeasurable (fun k : ↥(KG ε) =>
        F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) (muK ε) := by
    intro l hl z hz
    refine Measurable.aestronglyMeasurable ?_
    have e2 : (fun k : ↥(KG ε) => F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) =
        fun k => ∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
          (∏ j, (c (J j) ((toMK k)⁻¹ * l.get j * toMK k) : ℂ)) * F (List.ofFn fun j => b (J j)) (z * toMK k) := by
      funext k
      rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) _ (mul_mem_UJ hz (hK k))]
    rw [e2]
    refine Finset.measurable_sum _ fun J _ => Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ fun j _ =>
        Complex.measurable_ofReal.comp (hcc _ _ (hl _ (List.get_mem l j))).measurable
    · exact GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset n ε F hFd hF0c _ (hbw J) (↥(KG ε)) (fun k => z * toMK k)
        (continuous_const.matrix_mul (continuous_toMK ε)) fun k => mul_mem_UJ hz (hK k)
  obtain ⟨hA, hB⟩ := GlobalTheory.T.avg_derFam_growth_alt n ε N F hFd hUb hMs e he
  refine ⟨N, _, fun y hy => ?_, hA, hB⟩
  simp only [List.map_nil]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only
  rw [hF0 _ (mul_mem_UJ hy (hK k))]

end GlobalTheory.KAvgGrowth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageContinuousOnUniformModerateGrowthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactAverage_continuousOn_uniformModerateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  first | exact @GlobalTheory.KAvgGrowth.continuousOn_and_umg_kAvg | exact GlobalTheory.KAvgGrowth.continuousOn_and_umg_kAvg | (intros; apply GlobalTheory.KAvgGrowth.continuousOn_and_umg_kAvg <;> assumption)
end
end
