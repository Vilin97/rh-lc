module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Group.ModularCharacter
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainCoefficientSupportedPrincipalLevelStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralSplitFinitePlaceFubini

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Core.Rk.FubiniPlace



theorem integral_split_place : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (μ : Measure (GlobalTheory.FinZeta.Gv A v)), μ.IsHaarMeasure → ∀ J : Subgroup (GlobalTheory.FinZeta.Gv A v), IsOpen (J : Set (GlobalTheory.FinZeta.Gv A v)) → μ J = 1 → ∀ E : Set (GA D A), MeasurableSet E → (∀ x y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y ∈ E ↔ x ∈ E) → ∀ (F : GA D A → ℂ) (ζ : GlobalTheory.FinZeta.Gv A v → ℂ), Integrable ζ μ → (∀ y ∈ J, ζ y = 1) → (∀ x ∈ E, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y) = ζ y * F x) → IntegrableOn F (E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) m → IntegrableOn F E m ∧ ∫ g in E, F g ∂m = (∫ y, ζ y ∂μ) * ∫ g in E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}, F g ∂m := by
  intro D A m hm v μ hμ J hJo hJ1 E hE hEr F ζ hζ hζJ hF hFi
  have hec : Continuous (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_emb _ _ v
  have hpc : Continuous (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_proj _ _ v
  have hPm : MeasurableSet {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J} := (hJo.preimage hpc).measurableSet
  have hUm : MeasurableSet (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) := hE.inter hPm
  have hJm : MeasurableSet (J : Set (GlobalTheory.FinZeta.Gv A v)) := hJo.measurableSet

  have hright : ∀ k ∈ J, μ.map (fun y => y * k) = μ := by
    intro k hk
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
    have h2 := congrArg (fun m' : Measure (GlobalTheory.FinZeta.Gv A v) => m' (J : Set (GlobalTheory.FinZeta.Gv A v))) h
    simp only [Measure.coe_nnreal_smul_apply] at h2
    rw [Measure.map_apply (measurable_mul_const _) hJm,
      show (fun x => x * k) ⁻¹' (J : Set (GlobalTheory.FinZeta.Gv A v)) = J from Set.ext fun x => J.mul_mem_cancel_right hk,
      hJ1, mul_one] at h2
    have h3 : Measure.modularCharacterFun k = 1 := by exact_mod_cast h2.symm
    rw [h, h3, one_smul]

  have dec : ∀ x : GA D A, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) = 1 := by
    intro x; rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have dec2 : ∀ x : GA D A, x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x; rw [map_inv, inv_mul_cancel_right]
  have shift : ∀ (x : GA D A) (y : GlobalTheory.FinZeta.Gv A v),
      GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x y
    have hc := (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig A.gram y (dec x)).eq
    calc GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
          rw [mul_assoc, ← dec2]
      _ = _ := by rw [hc, mul_assoc, ← map_mul]
  have hEl : ∀ (y : GlobalTheory.FinZeta.Gv A v) (x : GA D A), GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x ∈ E ↔ x ∈ E := by
    intro y x
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    rw [shift, hEr, h1]
  have key : ∀ x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}), ∀ y, F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x) = F x * ζ (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x hx y
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    have hx' : x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ ∈ E := h1.1 hx.1
    have h2 := hF _ hx' (dec x) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h2
    rw [shift, hF _ hx' (dec x), h2, hζJ _ hx.2, one_mul, mul_comm]
  classical

  let c : GA D A → GlobalTheory.FinZeta.Gv A v := fun x => if GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J then GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x else 1
  have hcm : Measurable c := Measurable.ite hPm hpc.measurable measurable_const
  have hR : MeasurePreserving (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) (m.prod μ) (m.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun x y => y * c x) (MeasurePreserving.id m)
      (measurable_snd.mul (hcm.comp measurable_fst) : Measurable fun p : GA D A × GlobalTheory.FinZeta.Gv A v => p.2 * c p.1)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · simp only [c, if_pos hx]; exact hright _ hx
    · simp only [c, if_neg hx, mul_one, Measure.map_id']
  let g0 : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F q.1 * ζ q.2
  have hg0 : Integrable g0 (m.prod μ) := Integrable.mul_prod ((integrable_indicator_iff hUm).2 hFi) hζ
  let f : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * x)) q.1
  have hfg : f = g0 ∘ (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) := by
    funext q
    by_cases hx : q.1 ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J})
    · have hx2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1 ∈ J := hx.2
      simp only [f, g0, Function.comp_apply, c, if_pos hx2]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, key q.1 hx]
    · simp only [f, g0, Function.comp_apply, Set.indicator_of_notMem hx, zero_mul]
  have hf : Integrable f (m.prod μ) := by
    rw [hfg]; exact (hR.integrable_comp hg0.aestronglyMeasurable).2 hg0
  have hfint : ∫ q, f q ∂(m.prod μ) = ∫ q, g0 q ∂(m.prod μ) := by
    have h := integral_map (μ := m.prod μ) hR.measurable.aemeasurable (f := g0)
      (by rw [hR.map_eq]; exact hg0.aestronglyMeasurable)
    rw [hR.map_eq] at h
    rw [hfg]; exact h.symm

  let T : GA D A × GlobalTheory.FinZeta.Gv A v → GA D A × GlobalTheory.FinZeta.Gv A v := fun q => (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * q.1, q.2)
  have hTp : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2)) (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × GlobalTheory.FinZeta.Gv A v → GlobalTheory.FinZeta.Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : GlobalTheory.FinZeta.Gv A v × GA D A → GA D A × GlobalTheory.FinZeta.Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  let Te : (GA D A × GlobalTheory.FinZeta.Gv A v) ≃ᵐ (GA D A × GlobalTheory.FinZeta.Gv A v) :=
    { toFun := T
      invFun := fun q => ((GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2)⁻¹ * q.1, q.2)
      left_inv := fun q => by simp [T]
      right_inv := fun q => by simp [T]
      measurable_toFun := (((hec.comp continuous_snd).mul continuous_fst).prodMk continuous_snd).measurable
      measurable_invFun := ((((hec.comp continuous_snd).inv).mul continuous_fst).prodMk continuous_snd).measurable }
  have hT : MeasurePreserving Te (m.prod μ) (m.prod μ) := hTp
  let f₂ : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ :=
    fun q => {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) q
  have hf₂T : ∀ q, f₂ (Te q) = f q := by
    rintro ⟨x, y⟩
    have hp : (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y = (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    show {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) =
      (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x)) x
    by_cases h2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∈ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp]; exact J.inv_mem h2
      rw [Set.indicator_of_mem hq]
      by_cases h1 : x ∈ E
      · rw [Set.indicator_of_mem ((hEl y x).2 h1), Set.indicator_of_mem (show x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) from ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (hEl y x).1 h1), Set.indicator_of_notMem (by exact fun h => h1 h.1)]
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∉ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show ¬ (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp, inv_mem_iff]; exact h2
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (by exact fun h => h2 h.2)]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (hT.integrable_comp_emb Te.measurableEmbedding).1 ?_
    have : f₂ ∘ Te = f := funext hf₂T
    rw [this]; exact hf
  have hCm : ∀ a : GlobalTheory.FinZeta.Gv A v, MeasurableSet {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} :=
    fun a => (hJo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : GlobalTheory.FinZeta.Gv A v, μ {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} = 1 := by
    intro a
    rw [← hJ1]
    exact measure_preimage_mul μ a⁻¹ _
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = E.indicator F w := by
    intro w
    have : (fun y => f₂ (w, y)) = {y : GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ J}.indicator (fun _ => E.indicator F w) := by
      funext y; rfl
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hFE : Integrable (E.indicator F) m := by
    have h := hf₂.integral_prod_left
    simp_rw [inner] at h
    exact h
  refine ⟨(integrable_indicator_iff hE).1 hFE, ?_⟩
  calc ∫ g in E, F g ∂m = ∫ w, E.indicator F w ∂m := (integral_indicator hE).symm
    _ = ∫ q, f₂ q ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ q, f₂ (Te q) ∂(m.prod μ) := (hT.integral_comp' f₂).symm
    _ = ∫ q, f q ∂(m.prod μ) := by simp_rw [hf₂T]
    _ = ∫ q, g0 q ∂(m.prod μ) := hfint
    _ = (∫ x, (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F x ∂m) * ∫ y, ζ y ∂μ := integral_prod_mul _ _
    _ = _ := by rw [integral_indicator hUm, mul_comm]

end GlobalTheory.Core.Rk.FubiniPlace
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralSplitFinitePlaceFubiniStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.integral_split_finite_place_fubini : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (μ : Measure (GlobalTheory.FinZeta.Gv A v)), μ.IsHaarMeasure → ∀ J : Subgroup (GlobalTheory.FinZeta.Gv A v), IsOpen (J : Set (GlobalTheory.FinZeta.Gv A v)) → μ J = 1 → ∀ E : Set (GA D A), MeasurableSet E → (∀ x y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y ∈ E ↔ x ∈ E) → ∀ (F : GA D A → ℂ) (ζ : GlobalTheory.FinZeta.Gv A v → ℂ), Integrable ζ μ → (∀ y ∈ J, ζ y = 1) → (∀ x ∈ E, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y) = ζ y * F x) → IntegrableOn F (E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) m → IntegrableOn F E m ∧ ∫ g in E, F g ∂m = (∫ y, ζ y ∂μ) * ∫ g in E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}, F g ∂m := by
  first | exact @GlobalTheory.Core.Rk.FubiniPlace.integral_split_place | exact GlobalTheory.Core.Rk.FubiniPlace.integral_split_place | (intros; apply GlobalTheory.Core.Rk.FubiniPlace.integral_split_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoubling

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw.Peel

theorem qPeel_holds : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  intro hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz hlev
  classical
  have hhaar : s.ν.IsHaarMeasure := by
    obtain ⟨hr, -, hfl⟩ := hs
    exact hfl.haar
  have : BorelSpace (GA D s.V) := ⟨rfl⟩
  obtain ⟨-, hmO, hlevIff, -, -, -⟩ := GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs
  have hmL : MeasurableSet (levSet s) := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs).1
  set F := flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z with hF
  have hloc := GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz
  choose J μ ζ hJo hμ hμJ hζi hζ1 hJiff hζv hFx using hloc

  have hQPg : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => by rw [hw.union]; exact Finset.mem_union_right _ h
  have hQS : ∀ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := fun PP h => Finset.mem_image_of_mem _ (hQPg PP h)
  have hinj := GlobalTheory.LevelPlaces.injOn_under D c hw.com

  let cond : Pl D.host.E → GA D s.V → Prop := fun PP g => gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG s.V s.β s.L
  let ET : Finset (Pl D.host.E) → Set (GA D s.V) := fun T => intOff c s ∩ {g | ∀ PP ∈ T, cond PP g}
  have hET : ∀ T, T ⊆ w.Q → MeasurableSet (ET T) := by
    intro T hT
    have e : {g : GA D s.V | ∀ PP ∈ T, cond PP g} = ⋂ PP ∈ T, {g | cond PP g} := by ext g; simp
    refine hmO.inter ?_
    rw [e]
    refine Finset.measurableSet_biInter T fun PP hPP => ?_
    have e2 : {g : GA D s.V | cond PP g} = (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ⁻¹' (J PP (hT hPP) : Set _) := by
      ext g; exact hJiff PP (hT hPP) g
    rw [e2]
    exact ((hJo PP (hT hPP)).preimage (GlobalTheory.AdelicU.continuous_proj D.sp.cm.sig s.V.gram _)).measurableSet

  have hgAt : ∀ (v v' : HeightOneSpectrum (𝓞 D.host.F)), v' ≠ v → ∀ (x : GA D s.V) y,
      gAt s.V (.inl v') (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = gAt s.V (.inl v') x := by
    intro v v' hne x y
    show GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y)) =
      GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' x)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]
  have hOff : ∀ v ∈ c.S, ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ intOff c s ↔ x ∈ intOff c s := by
    intro v hv x y
    refine forall_congr' fun v' => imp_congr_right fun hv' => ?_
    have hne : v' ≠ v := fun h => hv' (h ▸ hv)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]

  have key : ∀ T : Finset (Pl D.host.E), T ⊆ w.Q → IntegrableOn F (ET w.Q) s.ν →
      IntegrableOn F (ET (w.Q \ T)) s.ν ∧ (z = (D.R.t : ℝ) / 2 → ∫ g in ET (w.Q \ T), F g ∂s.ν =
        (∏ PP ∈ T, blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) * ∫ g in ET w.Q, F g ∂s.ν) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ h; refine ⟨by simpa using h, fun _ => by simp⟩
    | insert PP T hPT ih =>
      intro hsub hint
      have hPP : PP ∈ w.Q := hsub (Finset.mem_insert_self _ _)
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert _ _).trans hsub) hint
      set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hvdef
      have hE' : MeasurableSet (ET (w.Q \ insert PP T)) := hET _ Finset.sdiff_subset
      have hinv : ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ ET (w.Q \ insert PP T) ↔
          x ∈ ET (w.Q \ insert PP T) := by
        intro x y
        refine and_congr (hOff v (hQS PP hPP) x y) (forall₂_congr fun PP' hPP' => ?_)
        have hne : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ v := by
          intro h
          have h1 := Finset.mem_sdiff.1 hPP'
          exact h1.2 (hinj (hQPg PP' h1.1) (hQPg PP hPP) h ▸ Finset.mem_insert_self _ _)
        show gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP'))) (x * _) ∈ _ ↔ gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP'))) x ∈ _
        rw [hgAt v _ hne]
      have hset : ET (w.Q \ insert PP T) ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ J PP hPP} = ET (w.Q \ T) := by
        ext g
        simp only [ET, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun PP' hPP' => ?_⟩
          by_cases he : PP' = PP
          · subst he; exact (hJiff PP' hPP g).2 h3
          · refine h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1, fun h => ?_⟩)
            rcases Finset.mem_insert.1 h with h | h
            · exact he h
            · exact (Finset.mem_sdiff.1 hPP').2 h
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, fun PP' hPP' => h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1,
            fun h => (Finset.mem_sdiff.1 hPP').2 (Finset.mem_insert_of_mem h)⟩)⟩, (hJiff PP hPP g).1 (h2 PP ?_)⟩
          exact Finset.mem_sdiff.2 ⟨hPP, hPT⟩
      have hFx' : ∀ x ∈ ET (w.Q \ insert PP T), GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v x = 1 → ∀ y,
          F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = ζ PP hPP y * F x :=
        fun x hx h1 y => hFx PP hPP x hx.1 h1 y
      have hfub := GlobalTheory.T.integral_split_finite_place_fubini D s.V s.ν hhaar v (μ PP hPP) (hμ PP hPP) (J PP hPP) (hJo PP hPP) (hμJ PP hPP)
        (ET (w.Q \ insert PP T)) hE' hinv F (ζ PP hPP) (hζi PP hPP) (hζ1 PP hPP) hFx' (by rw [hset]; exact ih1)
      refine ⟨hfub.1, fun hz2 => ?_⟩
      rw [hfub.2, hset, ih2 hz2, hζv PP hPP hz2, Finset.prod_insert hPT]
      ring

  have hsub : levSet s ⊆ ET w.Q := fun g hg => ⟨((hlevIff g).1 hg).1, fun PP hPP => ((hlevIff g).1 hg).2 _ (hQS PP hPP)⟩
  have hzero : ∀ g ∈ ET w.Q \ levSet s, F g = 0 := by
    rintro g ⟨⟨h1, h2⟩, h3⟩
    by_contra hne
    apply h3
    refine (hlevIff g).2 ⟨h1, fun v hv => ?_⟩
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    rw [hw.union] at hPP
    rcases Finset.mem_union.1 hPP with hP | hP
    · have hc : coefW p.ω m X (p.pt φ) g ≠ 0 := by
        intro h0
        apply hne
        simp only [hF, flatInt, GlobalTheory.Core.Rk.IP.integrand]
        rw [show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g from rfl, h0, zero_mul, zero_mul]
      exact GlobalTheory.T.twistedChain_coefficient_supported_principal_level D hgap c w hw k hk s s' hs hs' p hp m X hX φ g hc _
        (by simp only [Twist.S₀, Finset.coe_image]; exact Set.mem_image_of_mem _ hP)
    · exact h2 PP hP
  have hintR : IntegrableOn F (ET w.Q) s.ν := hlev.of_forall_diff_eq_zero (hET _ subset_rfl) hzero
  have hR := key w.Q subset_rfl hintR
  have hE0 : ET (w.Q \ w.Q) = intOff c s := by
    ext g; simp [ET]
  rw [hE0] at hR
  refine ⟨hR.1, fun hz2 => ?_⟩
  rw [hR.2 hz2, setIntegral_eq_of_subset_of_forall_diff_eq_zero (hET _ subset_rfl) hsub hzero]
  rfl

end GlobalTheory.ChainTw.Peel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoublingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chainTwistPlacesIntegralPeel_of_doubling : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  first | exact @GlobalTheory.ChainTw.Peel.qPeel_holds | exact GlobalTheory.ChainTw.Peel.qPeel_holds | (intros; apply GlobalTheory.ChainTw.Peel.qPeel_holds <;> assumption)
end
end
