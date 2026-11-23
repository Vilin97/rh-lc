module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFin

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory

noncomputable section

namespace GlobalTheory.SchrSuppFin

theorem exists_nhds_translate_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [NonarchimedeanAddGroup V] {f : V → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ U ∈ nhds (0 : V), ∀ u ∈ U, ∀ z, f (z + u) = f z := by
  have hW : ∀ x : V, ∃ W : OpenAddSubgroup V, ∀ w ∈ (W : Set V), f (x + w) = f x := by
    intro x
    have h1 : {w : V | f (x + w) = f x} ∈ nhds (0 : V) := by
      have h2 := (hf.comp_continuous (show Continuous (fun w : V => x + w) from continuous_const.add continuous_id)).eventually_eq 0
      simp only [Function.comp, add_zero] at h2
      exact h2
    obtain ⟨W, hW⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h1
    exact ⟨W, fun w hw => hW hw⟩
  choose W hW using hW
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun x => {z : V | z - x ∈ (W x : Set V)}) (fun x _ => by
    refine (continuous_sub_right x).continuousAt.preimage_mem_nhds ?_
    simpa using (W x).isOpen.mem_nhds (W x).zero_mem)
  refine ⟨⋂ x ∈ t, (W x : Set V), (Filter.biInter_finset_mem t).2 fun x _ => (W x).isOpen.mem_nhds (W x).zero_mem,
    fun u hu z => ?_⟩
  simp only [Set.mem_iInter] at hu
  by_cases hz : ∃ x ∈ t, z - x ∈ (W x : Set V)
  · obtain ⟨x, hx, hzx⟩ := hz
    have e1 := hW x (z - x) hzx
    have e2 := hW x (z + u - x) (by
      rw [show z + u - x = (z - x) + u by abel]; exact (W x).add_mem hzx (hu x hx))
    rw [show x + (z - x) = z by abel] at e1
    rw [show x + (z + u - x) = z + u by abel] at e2
    rw [e1, e2]
  · push_neg at hz
    have h1 : z ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      exact hz x hx hzx
    have h2 : z + u ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      refine hz x hx ?_
      have := (W x).sub_mem hzx (hu x hx)
      rwa [show z + u - x - u = z - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem nhdsNE_neBot {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by
  refine ⟨fun h => ?_⟩
  have hopen : IsOpen ({0} : Set (Fv F v)) := (isOpen_singleton_iff_punctured_nhds _).2 h
  haveI := discreteTopology_of_isOpen_singleton_zero hopen
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinf : ((v.adicCompletionIntegers F : Set (Fv F v))).Infinite :=
    Set.infinite_of_injective_forall_mem (Nat.cast_injective (R := Fv F v)) fun n => natCast_mem _ n
  exact hinf (hO.finite_of_discrete)

end GlobalTheory.SchrSuppFin

namespace GlobalTheory.SchrSuppFin

theorem support_compact : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  intro F _ _ v ψ₀ κ _ _ _ μ _ hψ hcond φ hφ g hg
  classical
  obtain ⟨hφl, hφc⟩ := hφ
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨Uφ, hUφ, hφU⟩ := exists_nhds_translate_eq hφl hφc
  obtain ⟨Ug, hUg, hgU⟩ := exists_nhds_translate_eq hgl hgc
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  have hP : ∀ᶠ s in nhds (0 : Fv F v), ∀ y ∈ (v.adicCompletionIntegers F : Set (Fv F v)), ∀ i : κ,
      (Pi.single i (s * y) : κ → Fv F v) ∈ Uφ ∩ Ug := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v) :=
      (continuous_single i).comp continuous_mul
    have hmem : Uφ ∩ Ug ∈ nhds ((fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v)) (0, y)) := by
      simpa using Filter.inter_mem hUφ hUg
    exact hc.continuousAt.preimage_mem_nhds hmem
  haveI := nhdsNE_neBot v
  obtain ⟨t, ht, ht0⟩ := ((hP.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (Fv F v))))).exists
  have ht0' : t ≠ 0 := ht0
  refine ⟨((fun p : (κ → Fv F v) × (κ → Fv F v) => p.1 - p.2) '' (tsupport φ ×ˢ tsupport g)) ×ˢ
    Set.pi Set.univ (fun _ => (fun y => t⁻¹ * y) '' (v.adicCompletionIntegers F : Set (Fv F v))), ?_, ?_⟩
  · exact ((hφc.isCompact.prod hgc.isCompact).image continuous_sub).prod
      (isCompact_univ_pi fun _ => hO.image (continuous_const_mul _))
  · rintro ⟨a, b⟩ hne
    have key : ∀ u ∈ Uφ ∩ Ug, ψ₀ (u ⬝ᵥ b) = 1 := by
      intro u hu
      have hG : ∀ y, schr ψ₀ (a, b) φ (y + u) * (starRingEnd ℂ) (g (y + u)) =
          ψ₀ (u ⬝ᵥ b) * (schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) := by
        intro y
        simp only [schr]
        rw [show y + u + a = (y + a) + u by abel, hφU u hu.1, hgU u hu.2, add_dotProduct,
          show y ⬝ᵥ b + u ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b) = u ⬝ᵥ b + (y ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b)) by ring,
          AddChar.map_add_eq_mul]
        ring
      have e := integral_add_right_eq_self (μ := μ)
        (fun y => schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) u
      simp only [hG] at e
      rw [integral_const_mul] at e
      have h0 : (ψ₀ (u ⬝ᵥ b) - 1) * ∫ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ∂μ = 0 := by
        rw [sub_mul, e]; ring
      exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hne)
    refine ⟨?_, ?_⟩
    · have hex : ∃ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (by simp [h])
      obtain ⟨y, hy⟩ := hex
      have h1 : φ (y + a) ≠ 0 := fun h => hy (by simp [schr, h])
      have h2 : g y ≠ 0 := fun h => hy (by simp [h])
      exact ⟨(y + a, y), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, by simp⟩
    · intro i _
      have hb : t * b i ∈ v.adicCompletionIntegers F := hcond _ fun y hy => by
        have := key _ (ht y hy i)
        rwa [single_dotProduct, show t * y * b i = t * b i * y by ring] at this
      exact ⟨t * b i, hb, by field_simp⟩

end GlobalTheory.SchrSuppFin

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFinStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory

theorem _root_.GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  first | exact @GlobalTheory.SchrSuppFin.support_compact | exact GlobalTheory.SchrSuppFin.support_compact | (intros; apply GlobalTheory.SchrSuppFin.support_compact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistence

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

open MeasureTheory ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagLocForm

section
variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem schr_adj (ψ₀ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ₀) {κ : Type} [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure]
    (w : (κ → Fv F v) × (κ → Fv F v)) (f g : (κ → Fv F v) → ℂ) :
    ∫ y, schr ψ₀ w f y * conj (g y) ∂μ = ∫ y, f y * conj (schr ψ₀ (-w) g y) ∂μ := by
  have h1 : ∀ s, conj (ψ₀ s) = ψ₀ (-s) := by
    intro s
    have h := GlobalTheory.norm_addChar_nonarch ψ₀ hψ s
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
    simp
  rw [← integral_add_right_eq_self (fun y => f y * conj (schr ψ₀ (-w) g y)) w.1]
  congr 1
  funext y
  have h2 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
  have e : -((y + w.1) ⬝ᵥ -w.2 + ⅟(2 : Fv F v) * (-w.1 ⬝ᵥ -w.2)) = y ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) := by
    simp only [add_dotProduct, dotProduct_neg, neg_dotProduct, neg_neg]
    linear_combination (-(w.1 ⬝ᵥ w.2)) * h2
  simp only [schr, Prod.fst_neg, Prod.snd_neg, map_mul, h1, add_neg_cancel_right]
  rw [e]; ring

theorem ip_self_ne {κ : Type} [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure] (g : (κ → Fv F v) → ℂ) (hg : g ∈ SB (κ → Fv F v))
    (h0 : g ≠ 0) : ∫ y, g y * conj (g y) ∂μ ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have e : (fun y => g y * conj (g y)) = fun y => ((Complex.normSq (g y) : ℝ) : ℂ) := by
    funext y; exact Complex.mul_conj (g y)
  rw [e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine ne_of_gt ?_
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := x)
    (Complex.continuous_normSq.comp hg.1.continuous) (hg.2.comp_left (g := Complex.normSq) (map_zero _))
    (fun y => Complex.normSq_nonneg _) ?_
  simpa using hx

end

theorem lagr_local_form : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  intro F _ _ v ψ₀ κ _ Λ Γ vac hψ hcond hiso hΓo hΓc hdual hvSB hv0 heig hfix
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  let μ : Measure (κ → Fv F v) := Measure.addHaar
  let c : ((κ → Fv F v) → ℂ) → ((κ → Fv F v) × (κ → Fv F v)) → ℂ :=
    fun φ w => ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ
  have hc : ∀ (φ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v)), c φ w = ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ := fun _ _ => rfl
  have schr_zero : ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ 0 φ = φ := by
    intro φ; funext x; simp [schr]
  have schr_add : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (φ₁ φ₂ : (κ → Fv F v) → ℂ), schr ψ₀ w (φ₁ + φ₂) = schr ψ₀ w φ₁ + schr ψ₀ w φ₂ := by
    intro w φ₁ φ₂; funext x; simp [schr, mul_add]
  have schr_smul : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (a : ℂ) (φ : (κ → Fv F v) → ℂ), schr ψ₀ w (a • φ) = a • schr ψ₀ w φ := by
    intro w a φ; funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  have comp_iso : ∀ w ∈ Λ, ∀ w' ∈ Λ, ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ w (schr ψ₀ w' φ) = schr ψ₀ (w + w') φ := by
    intro w hw w' hw' φ
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, hiso w hw w' hw', mul_zero, AddChar.map_zero_eq_one, one_smul]

  have hconst : ∀ φ : (κ → Fv F v) → ℂ, ∀ l ∈ Λ, ∀ γ ∈ Γ, γ ∈ Λ → c φ (l + γ) = c φ l := by
    intro φ l hl γ hγ hγΛ
    rw [hc, hc, add_comm, ← comp_iso γ hγΛ l hl, schr_adj ψ₀ hψ μ γ (schr ψ₀ l φ) vac,
      hfix (-γ) (AddSubgroup.mem_inf.2 ⟨Γ.neg_mem hγ, Λ.neg_mem hγΛ⟩)]
  let H : AddSubgroup Λ := Γ.addSubgroupOf Λ
  let ct : ((κ → Fv F v) → ℂ) → Λ ⧸ H → ℂ := fun φ =>
    Quotient.lift (s := QuotientAddGroup.leftRel H) (fun l : Λ => c φ l) (by
      intro a b hab
      have hab : -a + b ∈ H := QuotientAddGroup.leftRel_apply.1 hab
      rw [AddSubgroup.mem_addSubgroupOf] at hab
      have e : (b : (κ → Fv F v) × (κ → Fv F v)) = a + ((-a + b : Λ) : (κ → Fv F v) × (κ → Fv F v)) := by
        simp
      show c φ a = c φ b
      rw [e, hconst φ a a.2 _ hab (-a + b).2])
  have hct : ∀ (φ : (κ → Fv F v) → ℂ) (l : Λ), ct φ (l : Λ ⧸ H) = c φ l := fun _ _ => rfl

  have hfin : ∀ φ ∈ SB (κ → Fv F v), (Function.support (ct φ)).Finite := by
    intro φ hφ
    obtain ⟨C, hCc, hC⟩ := GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace v ψ₀ κ μ hψ hcond φ hφ vac hvSB
    obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun i : C => (fun z => z - (i : (κ → Fv F v) × (κ → Fv F v))) ⁻¹' Γ)
      (fun i => hΓo.preimage (continuous_sub_right _))
      (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by simp [Set.mem_preimage, sub_self, zero_mem]⟩)
    refine Set.Finite.subset (t.finite_toSet.biUnion fun i _ =>
      (Set.Subsingleton.finite (s := (QuotientAddGroup.mk : Λ → Λ ⧸ H) ''
        {l : Λ | (l : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ}) ?_)) ?_
    · rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have := Γ.sub_mem (show (l₂ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₂)
        (show (l₁ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₁)
      simpa [sub_sub_sub_cancel_right, neg_add_eq_sub] using this
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        rw [Function.mem_support, hct] at hq
        have hlC := hC _ hq
        obtain ⟨i, hi, hli⟩ := Set.mem_iUnion₂.1 (ht hlC)
        exact Set.mem_biUnion hi ⟨l, hli, rfl⟩
  have hint : ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      Integrable (fun y => schr ψ₀ w φ y * conj (vac y)) μ := by
    intro w φ hφ
    have h1 := GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ
    exact (h1.1.continuous.mul (Complex.continuous_conj.comp hvSB.1.continuous)).integrable_of_hasCompactSupport
      (hvSB.2.comp_left (g := conj) (map_zero _)).mul_left
  have ct_add : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ct (φ₁ + φ₂) = ct φ₁ + ct φ₂ := by
    intro φ₁ h₁ φ₂ h₂
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.add_apply, hc, schr_add, add_mul]
      exact integral_add (hint _ _ h₁) (hint _ _ h₂)
  have ct_smul : ∀ (a : ℂ) (φ : (κ → Fv F v) → ℂ), ct (a • φ) = a • ct φ := by
    intro a φ
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.smul_apply, smul_eq_mul, hc, schr_smul, mul_assoc]
      exact integral_const_mul a _
  let l₀ : SB (κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ᶠ q, ct φ q
      map_add' := fun φ₁ φ₂ => by
        show ∑ᶠ q, ct ((φ₁ : (κ → Fv F v) → ℂ) + φ₂) q = ∑ᶠ q, ct φ₁ q + ∑ᶠ q, ct φ₂ q
        rw [ct_add _ φ₁.2 _ φ₂.2]
        exact finsum_add_distrib (hfin _ φ₁.2) (hfin _ φ₂.2)
      map_smul' := fun a φ => by
        show ∑ᶠ q, ct (a • (φ : (κ → Fv F v) → ℂ)) q = (RingHom.id ℂ) a • ∑ᶠ q, ct φ q
        rw [ct_smul, RingHom.id_apply, smul_eq_mul, mul_finsum]
        rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  have hl' : ∀ φ (hφ : φ ∈ SB (κ → Fv F v)), l φ = ∑ᶠ q, ct φ q := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun w hw φ hφ => ?_, ?_⟩
  · rw [hl' _ (GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ), hl' φ hφ]
    have e : ct (schr ψ₀ w φ) = fun q => ct φ (q + ((⟨w, hw⟩ : Λ) : Λ ⧸ H)) := by
      funext q
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        rw [← QuotientAddGroup.mk_add, hct, hct, hc, hc, comp_iso m m.2 w hw]
        rfl
    rw [e]
    exact finsum_comp_equiv (Equiv.addRight _)
  · have hX0 : c vac 0 ≠ 0 := by
      rw [hc, schr_zero]; exact ip_self_ne μ vac hvSB hv0
    have hd : ∀ w, c vac w ≠ 0 → w ∈ Γ := by
      intro w hw
      rw [hdual]
      intro γ hγ
      obtain ⟨a, ha⟩ := heig γ hγ
      have hinv : a • schr ψ₀ (-γ) vac = vac := by
        rw [← schr_smul, ← ha, GlobalTheory.ThetaQuasiRat.schr_schr, neg_add_cancel, schr_zero]
        have : (-γ).1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ (-γ).2 = 0 := by
          simp only [Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg]; ring
        rw [this, mul_zero, AddChar.map_zero_eq_one, one_smul]
      have ha0 : a ≠ 0 := by
        rintro rfl; apply hv0; rw [← hinv, zero_smul]
      have hneg : schr ψ₀ (-γ) vac = a⁻¹ • vac := by
        rw [← hinv, smul_smul, inv_mul_cancel₀ ha0, one_smul, hinv]
      have key : ∀ w : (κ → Fv F v) × (κ → Fv F v),
          ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a * c vac w = conj a⁻¹ * c vac w := by
        intro w
        have e1 : schr ψ₀ γ (schr ψ₀ w vac) = (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) • schr ψ₀ w vac := by
          have h1 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ γ w vac
          have h2 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ w γ vac
          rw [ha, schr_smul, add_comm w γ] at h2
          rw [h1, mul_smul, h2, smul_smul, ← AddChar.map_add_eq_mul]
          have h3 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
          have e4 : ⅟(2 : Fv F v) * (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) =
              (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) := by
            linear_combination (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * h3
          rw [e4]
        have e3 : ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ =
            ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
          calc ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ
              = ∫ y, schr ψ₀ γ (schr ψ₀ w vac) y * conj (vac y) ∂μ := by
                congr 1; funext y; rw [e1, Pi.smul_apply, smul_eq_mul]; ring
            _ = ∫ y, schr ψ₀ w vac y * conj (schr ψ₀ (-γ) vac y) ∂μ := schr_adj ψ₀ hψ μ γ _ vac
            _ = ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
                congr 1; funext y; rw [hneg, Pi.smul_apply, smul_eq_mul, map_mul]; ring
        rw [integral_const_mul, integral_const_mul] at e3
        rw [hc]; exact e3
      have haa : a = conj a⁻¹ := by
        have k0 := key 0
        simp only [Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero,
          AddChar.map_zero_eq_one, one_mul] at k0
        exact mul_right_cancel₀ hX0 k0
      have hk := key w
      rw [← haa] at hk
      have hψω : ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) = 1 := by
        have := mul_right_cancel₀ hw hk
        exact mul_right_cancel₀ ha0 (by rw [this, one_mul])
      rw [show w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2 = -(γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) by ring, AddChar.map_neg_eq_inv, hψω, inv_one]
    rw [hl' vac hvSB, finsum_eq_single _ (0 : Λ ⧸ H)]
    · show ct vac ((0 : Λ) : Λ ⧸ H) ≠ 0
      rw [hct]; simpa using hX0
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        by_contra hm
        rw [hct] at hm
        exact hq ((QuotientAddGroup.eq_zero_iff m).2 (AddSubgroup.mem_addSubgroupOf.2 (hd m hm)))

end GlobalTheory.LagLocForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistenceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  first | exact @GlobalTheory.LagLocForm.lagr_local_form | exact GlobalTheory.LagLocForm.lagr_local_form | (intros; apply GlobalTheory.LagLocForm.lagr_local_form <;> assumption)
end
end
