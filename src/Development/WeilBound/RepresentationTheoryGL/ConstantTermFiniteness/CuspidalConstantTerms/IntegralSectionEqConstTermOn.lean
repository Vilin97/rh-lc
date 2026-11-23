module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdHomeoSymmApplySnd
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Dynamics.Ergodic.Action.Regular

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasure

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.Cusp.Shear

theorem isFundamentalDomain_image_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  intro G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ
    A B hAm hBm hA hB ν
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he
  have himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B) := by
    ext n; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨e.symm n, h, by simp⟩
  have efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹ := fun n => rfl
  have esnd : ∀ n : N, (e.symm n).2 = π n := fun n => rfl
  refine IsFundamentalDomain.mk' ?_ ?_
  · rw [himg]; exact (e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet
  · intro x
    have hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B := by
      intro n; rw [himg]; rfl
    have hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) =
        (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹) := by
      intro g
      rw [efst, hπmul, hsadd]
      simp only [Subgroup.coe_mul]
      group
    have hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x := fun g => by rw [esnd, hπmul]
    let c : V → N' := fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹,
      hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩
    obtain ⟨w, hwB, hwu⟩ := hB (π x)
    obtain ⟨δ, hδA, hδu⟩ := hA (c w)
    have hδΓ : ((δ : N') : G) ∈ Γ := Subgroup.mem_subgroupOf.1 δ.2
    let γ0 : Γ.subgroupOf N := ⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩,
      Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩
    have hπγ0 : π (γ0 : N) = w := by
      have h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩ := rfl
      rw [h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]
    refine ⟨γ0, ?_, ?_⟩
    · show (γ0 : N) * x ∈ _
      rw [hmemS, hsnd, hπγ0]
      refine ⟨?_, hwB⟩
      have h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w := by
        apply Subtype.ext
        rw [hfst, hπγ0]
        show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)
        group
      rw [h]; exact hδA
    · intro γ hγ
      have hγ' : (γ : N) * x ∈ e '' (A ×ˢ B) := hγ
      rw [hmemS, hsnd] at hγ'
      obtain ⟨hγA, hγB⟩ := hγ'
      have hγΓ : ((γ : N) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      have hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w := hwu _ hγB
      have hwv : π (γ : N) = w := congrArg Subtype.val hw
      have hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N' := hwv ▸ mul_inv_mem hs hπmul hπs hker γ
      let δγ : Γ.subgroupOf N' := ⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩,
        Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩
      have h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1 := by
        apply Subtype.ext
        rw [hfst, hwv]
        rfl
      have hδe : δγ = δ := hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)
      have hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G) := by
        rw [← hδe]
      apply Subtype.ext; apply Subtype.ext
      show ((γ : N) : G) = ((δ : N') : G) * s w
      rw [← hv]; group

end GlobalTheory.Cusp.Shear
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibration

section

@[expose] public section

open MeasureTheory

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem isHaarMeasure_map_prodHomeo : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  intro G _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ _ _ s π hs hsc hπc hπmul hπs hker hsmul μ hμ
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he_def
  set P : Measure (N' × V) := (Measure.haar : Measure N').prod μ with hP
  set ν : Measure N := P.map e with hν
  haveI := hc'.isMulRightInvariant (Measure.haar : Measure N')
  have hem : Measurable e := e.continuous.measurable
  haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map P e
  haveI : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective

  haveI hR : ν.IsMulRightInvariant := ⟨fun n₀ => by
    set z₀ := e.symm n₀
    have hz₀ : ((n₀ : N) : G) = (z₀.1 : G) * s z₀.2 := by
      rw [← prodHomeo_apply hle hs hsc hπc hπmul hπs hker z₀]; simp [z₀, e]
    let c : V → N' := fun v => ⟨s v * z₀.1 * (s v)⁻¹, hn _ (hs v) _ z₀.1.2⟩
    have hcc : Continuous c := by fun_prop
    let T' : V × N' → V × N' := fun p => (p.1 + z₀.2, p.2 * c p.1)
    have hT' : MeasurePreserving T' (μ.prod (Measure.haar : Measure N')) (μ.prod (Measure.haar : Measure N')) :=
      (measurePreserving_add_right μ z₀.2).skew_product (g := fun v m => m * c v)
        (by apply Continuous.measurable; fun_prop)
        (.of_forall fun v => map_mul_right_eq_self _ _)
    have hT : MeasurePreserving (Prod.swap ∘ T' ∘ Prod.swap) P P :=
      Measure.measurePreserving_swap.comp (hT'.comp Measure.measurePreserving_swap)
    have hcomm : (fun n => n * n₀) ∘ e = e ∘ (Prod.swap ∘ T' ∘ Prod.swap) := by
      funext ⟨m, v⟩
      apply Subtype.ext
      change ((m : G) * s v) * (n₀ : G) = ((m * c v : N') : G) * s (v + z₀.2)
      rw [hz₀, hsmul, Subgroup.coe_mul]
      change _ = (m : G) * (s v * (z₀.1 : G) * (s v)⁻¹) * (s v * s z₀.2)
      group
    rw [hν, Measure.map_map (measurable_mul_const n₀) hem, hcomm, ← Measure.map_map hem hT.measurable, hT.map_eq]⟩
  haveI : IsFiniteMeasureOnCompacts ν.inv := Measure.IsFiniteMeasureOnCompacts.map ν (Homeomorph.inv N)
  haveI : ν.inv.IsOpenPosMeasure := (Homeomorph.inv N).continuous.isOpenPosMeasure_map (Homeomorph.inv N).surjective
  haveI : ν.inv.IsHaarMeasure := {}
  haveI := hc.isMulRightInvariant ν.inv
  have hL : ν.IsMulLeftInvariant := by rw [← Measure.inv_inv ν]; infer_instance
  exact {}

end GlobalTheory.Cusp.Shear

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.IntegralSectionEqConstTermOn

section

@[expose] public section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Cusp.Shear.Rg

theorem exists_measurable_addSection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N : Subgroup G) [DiscreteTopology Γ]
    (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) (s : V → G) (π : N → V), Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) →
    (∀ (a : N) (v : V), (a : G) = s v → π a = v) → (∀ v ∈ Λ, s v ∈ Γ) →
    ∃ B : Set V, MeasurableSet B ∧ ∀ v : V, ∃! w : Λ, (w : V) + v ∈ B := by
  intro G _ _ _ _ _ _ Γ N _ V _ _ _ _ Λ s π hsc hmul hs hπs hsΓ
  let s' : V → N := fun v => ⟨s v, hs v⟩
  have hπs' : ∀ v, π (s' v) = v := fun v => hπs _ v rfl
  have hs'add : ∀ v w, s' (v + w) = s' v * s' w := fun v w => Subtype.ext (hmul v w)
  have hs0 : s' 0 = 1 := by
    have h := hs'add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

  let H : Subgroup N :=
    { carrier := {n | n = s' (π n) ∧ π n ∈ Λ}
      one_mem' := by
        have h1 : π 1 = 0 := by rw [← hs0, hπs']
        exact ⟨by rw [h1, hs0], by rw [h1]; exact Λ.zero_mem⟩
      mul_mem' := fun {a b} ha hb => by
        have e : a * b = s' (π a + π b) := by rw [hs'add, ← ha.1, ← hb.1]
        have hp : π (a * b) = π a + π b := by rw [e, hπs']
        exact ⟨by rw [hp]; exact e, by rw [hp]; exact Λ.add_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => by
        have h1 : s' (π a) * s' (-π a) = 1 := by rw [← hs'add, add_neg_cancel, hs0]
        have e : a⁻¹ = s' (-π a) :=
          (congrArg (·⁻¹) ha.1).trans (eq_inv_of_mul_eq_one_right h1).symm
        have hp : π a⁻¹ = -π a := by rw [e, hπs']
        exact ⟨by rw [hp]; exact e, by rw [hp]; exact Λ.neg_mem ha.2⟩ }
  have hH : ∀ h : H, ((h : N) : G) ∈ Γ := fun h => by
    have e : ((h : N) : G) = s (π h) := congrArg Subtype.val h.2.1
    rw [e]; exact hsΓ _ h.2.2
  haveI : DiscreteTopology H :=
    .of_continuous_injective (f := fun h : H => (⟨((h : N) : G), hH h⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      fun a b e => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) e))
  refine ⟨s' ⁻¹' stdDom H, (hsc.subtype_mk hs).measurable (measurableSet_stdDom H), fun v => ?_⟩
  obtain ⟨h, hh, hu⟩ := existsUnique_stdDom H (s' v)
  refine ⟨⟨π h, h.2.2⟩, ?_, fun w hw => ?_⟩
  · show s' (π h + v) ∈ stdDom H
    rw [hs'add, ← h.2.1]
    exact hh
  · have hmem : s' w ∈ H := ⟨by rw [hπs'], by rw [hπs']; exact w.2⟩
    have e := hu ⟨s' w, hmem⟩ (by
      show s' w * s' v ∈ stdDom H
      rw [← hs'add]
      exact hw)
    apply Subtype.ext
    show (w : V) = π h
    rw [← e]
    exact (hπs' w).symm

theorem integral_section_eq_constTermOn : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ]
    [LocallyCompactSpace N] [LocallyCompactSpace N'], N' ≤ N → (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [MeasurableSpace V] [BorelSpace V] (Λ : AddSubgroup V) (s : V → G) (π : N → V),
      Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) → Continuous π →
      (∀ a b : N, π (a * b) = π a + π b) → (∀ (a : N) (v : V), (a : G) = s v → π a = v) →
      (∀ a : N, π a = 0 ↔ (a : G) ∈ N') → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ φ : G → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ φ → Continuous φ → (∀ m ∈ N', ∀ g, φ (m * g) = φ g) →
      ∀ (μ : MeasureTheory.Measure V) (𝓕 : Set V), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Λ 𝓕 μ →
        ∀ x : G, ∫ v in 𝓕, φ (s v * x) ∂μ = μ.real 𝓕 • GlobalTheory.Cusp.constTermOn Γ N φ x := by
  intro G _ _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ Λ s π hsc hmul hs hπc hπmul hπs hker hsΓ hπΓ
    φ hφ hφc hN' μ 𝓕 hμ h𝓕 x

  let s' : V → N := fun v => ⟨s v, hs v⟩
  have hs'c : Continuous s' := hsc.subtype_mk _
  have hleft : Function.LeftInverse π s' := fun v => hπs _ v rfl
  have hemb : Topology.IsEmbedding s' := hleft.isEmbedding hπc hs'c
  haveI : SecondCountableTopology V := hemb.secondCountableTopology
  haveI : T2Space V := hemb.t2Space
  haveI : Countable Λ := Function.Injective.countable (f := fun w : Λ => (⟨s w, hsΓ _ w.2⟩ : Γ)) fun a b h =>
    Subtype.ext (hleft.injective (Subtype.ext (congrArg Subtype.val h : s a = s b)))
  let e := prodHomeo hle hs hsc hπc hπmul hπs hker
  let ν : Measure N := ((Measure.haar : Measure N').prod μ).map e
  haveI : ν.IsHaarMeasure := isHaarMeasure_map_prodHomeo G Γ N N' hle hn hc hc' V s π hs hsc hπc hπmul hπs hker hmul μ hμ
  obtain ⟨B, hBm, hB⟩ := exists_measurable_addSection G Γ N V Λ s π hsc hmul hs hπs hsΓ
  let A := stdDom (Γ.subgroupOf N')
  have hAm : MeasurableSet A := measurableSet_stdDom _
  have hD : IsFundamentalDomain (Γ.subgroupOf N) (e '' (A ×ˢ B)) ν :=
    isFundamentalDomain_image_prod G Γ N N' hle hn V Λ s π hs hsc hπc hπmul hπs hker hmul hsΓ hπΓ A B hAm hBm
      (existsUnique_stdDom _) hB ν
  have hep : MeasurePreserving e ((Measure.haar : Measure N').prod μ) ν := ⟨e.continuous.measurable, rfl⟩
  have hemb' : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding

  have hI : ∫ n in e '' (A ×ˢ B), φ (n * x) ∂ν =
      (Measure.haar : Measure N').real A • ∫ v in B, φ (s v * x) ∂μ := by
    rw [hep.setIntegral_image_emb hemb', ← Measure.prod_restrict]
    have h1 : ∀ z : N' × V, φ ((e z : G) * x) = φ (s z.2 * x) := fun z => by
      rw [prodHomeo_apply, mul_assoc]; exact hN' _ z.1.2 _
    simp only [h1]
    rw [integral_fun_snd (fun v => φ (s v * x)), measureReal_restrict_apply_univ]
  have hM : ν (e '' (A ×ˢ B)) = Measure.haar A * μ B := by
    change ((Measure.haar : Measure N').prod μ).map e _ = _
    rw [hemb'.map_apply, e.preimage_image, Measure.prod_prod]
  have hA0 : (Measure.haar : Measure N') A ≠ 0 := (isFundamentalDomain_stdDom _ _).measure_ne_zero (NeZero.ne _)
  have hAt : (Measure.haar : Measure N') A ≠ ⊤ := hc'.measure_ne_top (isFundamentalDomain_stdDom _ _)
  have hDt := hc.measure_ne_top hD
  have hD0 := hD.measure_ne_zero (NeZero.ne ν)
  rw [hM] at hDt hD0
  have hBt : μ B ≠ ⊤ := fun h => hDt (by rw [h, ENNReal.mul_top hA0])
  have hB0 : μ B ≠ 0 := fun h => hD0 (by rw [h, mul_zero])

  have hBF : IsAddFundamentalDomain Λ B μ := .mk' hBm.nullMeasurableSet fun v => by
    simpa [AddSubgroup.vadd_def, vadd_eq_add] using hB v
  have hf : ∀ (w : Λ) (v : V), φ (s ((w : V) + v) * x) = φ (s v * x) := fun w v => by
    rw [hmul, mul_assoc]; exact hφ _ (hsΓ _ w.2) _
  rw [h𝓕.setIntegral_eq hBF (fun w v => hf w v), measureReal_def, h𝓕.measure_eq hBF, constTermOn_eq hD hφ x, hI,
    measureReal_def, hM, measureReal_def, ENNReal.toReal_mul, smul_smul, smul_smul]
  have ha : ((Measure.haar : Measure N') A).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hA0, hAt⟩
  have hb : (μ B).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hB0, hBt⟩
  rw [show (μ B).toReal * (((Measure.haar : Measure N') A).toReal * (μ B).toReal)⁻¹ *
      ((Measure.haar : Measure N') A).toReal = 1 by field_simp, one_smul]

end GlobalTheory.Cusp.Shear.Rg

end
end
end
