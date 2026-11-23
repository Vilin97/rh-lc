module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SumCoset
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.VolIdx
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.AvgInt

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem avgInt : AvgInt := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 U hUo F hF q
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set u : K → ℂ := fun y => F (q * (y : G)) with hu
  set S : Subgroup K := GlobalTheory.BCT.rStab u with hS
  have hUS : U.subgroupOf K ≤ S := by
    intro k hk
    have hk' : (k : G) ∈ U := Subgroup.mem_subgroupOf.mp hk
    show ∀ x : K, u (x * k) = u x
    intro x
    simp only [hu, Subgroup.coe_mul, ← mul_assoc]
    exact hF _ hk' _
  have hSo : IsOpen (S : Set K) := Subgroup.isOpen_mono hUS (Subgroup.subgroupOf_isOpen K U hUo)
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  have hconst : ∀ y : K, u y = u (Quotient.out (QuotientGroup.mk y : K ⧸ S)) := by
    intro y
    have hmem : (Quotient.out (QuotientGroup.mk y : K ⧸ S))⁻¹ * y ∈ S := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have h := hmem (Quotient.out (QuotientGroup.mk y : K ⧸ S))
    rw [mul_inv_cancel_left] at h
    exact h
  set S' : Set G := ((↑) : K → G) '' (S : Set K) with hS'
  have hS'o : IsOpen S' := hKo.isOpenMap_subtype_val _ hSo
  set A : K ⧸ S → Set G := fun c => (fun y => ((Quotient.out c : K) : G)⁻¹ * y) ⁻¹' S' with hA
  have hmemA : ∀ c y, y ∈ A c ↔ ∃ h : y ∈ K, (QuotientGroup.mk (⟨y, h⟩ : K) : K ⧸ S) = c := by
    intro c y
    simp only [hA, hS', Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨s, hs, hsy⟩
      have hy : y = ((Quotient.out c : K) : G) * (s : G) := by
        rw [hsy]
        group
      have hyK : y ∈ K := by
        rw [hy]
        exact K.mul_mem (Quotient.out c).2 s.2
      refine ⟨hyK, ?_⟩
      have he : (⟨y, hyK⟩ : K) = Quotient.out c * s := Subtype.ext hy
      rw [he]
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hs
    · rintro ⟨hyK, hc⟩
      have hmem : (Quotient.out c)⁻¹ * (⟨y, hyK⟩ : K) ∈ S := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hc]
      exact ⟨_, hmem, by simp⟩
  have hAm : ∀ c, MeasurableSet (A c) := fun c => (measurable_const_mul _) hS'o.measurableSet
  have hAK : ∀ c, A c ⊆ K := fun c y hy => ((hmemA c y).mp hy).1
  have hAμ : ∀ c, μ (A c) = μ S' := fun c => measure_preimage_mul μ _ S'
  have hunion : (⋃ c, A c) = (K : Set G) := by
    apply Set.Subset.antisymm (Set.iUnion_subset hAK)
    intro y hy
    exact Set.mem_iUnion.mpr ⟨_, (hmemA _ y).mpr ⟨hy, rfl⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro c c' hcc'
    refine Set.disjoint_left.mpr fun y h1 h2 => hcc' ?_
    obtain ⟨h, rfl⟩ := (hmemA c y).mp h1
    obtain ⟨h', rfl⟩ := (hmemA c' y).mp h2
    rfl
  have hsum : (Fintype.card (K ⧸ S) : ℝ≥0∞) * μ S' = 1 := by
    rw [← hK1, ← hunion, measure_iUnion hdisj hAm, tsum_fintype]
    simp only [hAμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ S) : ℕ) = S.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hreal : ∀ c, μ.real (A c) = ((S.index : ℝ))⁻¹ := by
    intro c
    have hne : (Fintype.card (K ⧸ S) : ℝ≥0∞) ≠ 0 := by
      simp
    have h1 : μ S' = ((Fintype.card (K ⧸ S) : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.eq_div_iff hne (by simp), ENNReal.div_eq_inv_mul, mul_one] at hsum
      exact hsum
    rw [Measure.real, hAμ, h1, ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard]
  haveI : IsFiniteMeasure (μ.restrict (K : Set G)) :=
    ⟨by rw [Measure.restrict_apply_univ, hK1]; exact ENNReal.one_lt_top⟩
  have hint : ∫ y in (K : Set G), F (q * y) ∂μ =
      ∫ y in (K : Set G), ∑ c, (A c).indicator (fun _ => u (Quotient.out c)) y ∂μ := by
    refine setIntegral_congr_fun hKo.measurableSet fun y hy => ?_
    rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : K) : K ⧸ S)]
    · rw [Set.indicator_of_mem ((hmemA _ y).mpr ⟨hy, rfl⟩)]
      exact hconst ⟨y, hy⟩
    · intro c _ hc
      refine Set.indicator_of_notMem (fun h => hc ?_) _
      obtain ⟨h', rfl⟩ := (hmemA c y).mp h
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hint, integral_finsetSum _ fun c _ => (integrable_const _).indicator (hAm c)]
  unfold GlobalTheory.BCT.avg
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_indicator_const _ (hAm c), measureReal_restrict_apply (hAm c),
    Set.inter_eq_left.mpr (hAK c), hreal c, Complex.real_smul]
  push_cast
  rfl

end UpperTheory.Gal.InertialTypesAlt.L
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OneCoset

section

@[expose] public section

open MeasureTheory PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb
open scoped ENNReal

theorem UpperTheory.Gal.InertialTypesAlt.L.oneCoset :
    UpperTheory.Gal.InertialTypesAlt.L.OneCoset := by
  classical
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hTcomm ν hν F hF hFT q
  haveI := hμ
  haveI := hν
  obtain ⟨hsf, hinv, hright⟩ := haarComm_holds G T hTc hTcomm ν hν
  haveI := hsf
  haveI := hinv
  haveI := hright
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hright
  set D : Set G := {g | ∃ t ∈ T, ∃ y ∈ K, g = t * q * y} with hD
  set Hs : Set T := {t : T | q⁻¹ * (t : G) * q ∈ K} with hHs
  set qK : Set G := {g | q⁻¹ * g ∈ K} with hqK

  have hqKo : IsOpen qK := hKo.preimage (continuous_const.mul continuous_id)
  have hDo : IsOpen D := by
    have : D = ⋃ t : T, (fun g : G => ((t : G) * q)⁻¹ * g) ⁻¹' (K : Set G) := by
      ext g
      simp only [hD, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · rintro ⟨t, ht, y, hy, rfl⟩
        refine ⟨⟨t, ht⟩, ?_⟩
        simpa [mul_assoc] using hy
      · rintro ⟨t, ht⟩
        exact ⟨t, t.2, _, ht, by group⟩
    rw [this]
    exact isOpen_iUnion fun t => hKo.preimage (continuous_const.mul continuous_id)
  have hHo : IsOpen Hs :=
    hKo.preimage (((continuous_const.mul continuous_subtype_val).mul continuous_const))
  have hHc : IsCompact Hs := by
    have hS : IsCompact ((fun x : G => q * x * q⁻¹) '' (K : Set G)) :=
      hKc.image (by fun_prop)
    have hpc := hTc.isClosedEmbedding_subtypeVal.isCompact_preimage hS
    have e : Hs = Subtype.val ⁻¹' ((fun x : G => q * x * q⁻¹) '' (K : Set G)) := by
      ext t
      simp only [hHs, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro h
        exact ⟨_, h, by group⟩
      · rintro ⟨x, hx, hxt⟩
        have : q⁻¹ * (t : G) * q = x := by rw [← hxt]; group
        rwa [this]
    rw [e]
    exact hpc
  have h1H : (1 : T) ∈ Hs := by
    simpa [hHs] using K.one_mem
  set v : ℝ≥0∞ := ν Hs with hv
  have hv0 : v ≠ 0 := hHo.measure_ne_zero ν ⟨1, h1H⟩
  have hvt : v ≠ ∞ := hHc.measure_lt_top.ne
  have hqKD : qK ⊆ D := fun g hg => ⟨1, T.one_mem, q⁻¹ * g, hg, by group⟩
  have hDT : ∀ h ∈ T, ∀ g, h * g ∈ D ↔ g ∈ D := by
    intro h hh g
    constructor
    · rintro ⟨t, ht, y, hy, e⟩
      refine ⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, y, hy, ?_⟩
      calc g = h⁻¹ * (h * g) := by group
        _ = _ := by rw [e]; group
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨h * t, T.mul_mem hh ht, y, hy, by group⟩
  set ρ' : G → ℝ≥0∞ := D.piecewise (qK.indicator fun _ => v⁻¹) ρ with hρ'def
  have hρ' : IsQuotNormaliser T ν ρ' := by
    refine ⟨Measurable.piecewise hDo.measurableSet
      (measurable_const.indicator hqKo.measurableSet) hρ.1, fun g => ?_⟩
    by_cases hg : g ∈ D
    · obtain ⟨t₀, ht₀, y, hy, rfl⟩ := hg
      set A : Set T := (fun h : T => h * (⟨t₀, ht₀⟩ : T)) ⁻¹' Hs with hA
      have hAm : MeasurableSet A := (hHo.preimage (continuous_mul_const _)).measurableSet
      have hpt : ∀ h : T, ρ' ((h : G) * (t₀ * q * y)) = A.indicator (fun _ => v⁻¹) h := by
        intro h
        have hmem : (h : G) * (t₀ * q * y) ∈ D :=
          (hDT _ h.2 _).2 ⟨t₀, ht₀, y, hy, rfl⟩
        rw [hρ'def, Set.piecewise_eq_of_mem _ _ _ hmem]
        have hiff : (h : G) * (t₀ * q * y) ∈ qK ↔ h ∈ A := by
          have e : q⁻¹ * ((h : G) * (t₀ * q * y)) = (q⁻¹ * ((h : G) * t₀) * q) * y := by group
          simp only [hqK, hA, hHs, Set.mem_setOf_eq, Set.mem_preimage, e, Subgroup.coe_mul]
          exact Subgroup.mul_mem_cancel_right K hy
        by_cases hh : h ∈ A
        · rw [Set.indicator_of_mem (hiff.2 hh), Set.indicator_of_mem hh]
        · rw [Set.indicator_of_notMem (fun c => hh (hiff.1 c)), Set.indicator_of_notMem hh]
      simp_rw [hpt]
      rw [lintegral_indicator_const hAm, hA, measure_preimage_mul_right, ← hv]
      exact ENNReal.inv_mul_cancel hv0 hvt
    · have hpt : ∀ h : T, ρ' ((h : G) * g) = ρ ((h : G) * g) := by
        intro h
        rw [hρ'def, Set.piecewise_eq_of_notMem _ _ _ (fun c => hg ((hDT _ h.2 _).1 c))]
      simp_rw [hpt]
      exact hρ.2 g
  have hFm : Measurable (D.indicator F) := hF.measurable.indicator hDo.measurableSet
  have hFinv : ∀ h ∈ T, ∀ g, D.indicator F (h * g) = D.indicator F g := by
    intro h hh g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hDT h hh g).2 hg), hFT h hh]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg ((hDT h hh g).1 c))]
  rw [quotIndep_holds G μ hμ T ν hsf hinv _ hFm hFinv ρ' hρ']
  have hpt : ∀ g, D.indicator F g * ((ρ' g).toReal : ℂ) =
      qK.indicator (fun g => ((v.toReal : ℝ) : ℂ)⁻¹ * F g) g := by
    intro g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, hρ'def, Set.piecewise_eq_of_mem _ _ _ hg]
      by_cases hq : g ∈ qK
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, ENNReal.toReal_inv]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
        simp
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg (hqKD c)), zero_mul]
  simp_rw [hpt]
  rw [integral_indicator hqKo.measurableSet, integral_const_mul]
  have hpre : (fun y : G => q * y) ⁻¹' qK = (K : Set G) := by
    ext y
    simp [hqK]
  have := (measurePreserving_mul_left μ q).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft q) F qK
  rw [hpre] at this
  rw [this]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbSum

section

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem continuous_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (F : G → ℂ) (h : ∀ u ∈ U, ∀ x, F (x * u) = F x) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hev : F =ᶠ[nhds x] fun _ => F x := by
    have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (U : Set G)) :=
      hU.preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y => x⁻¹ * y) ⁻¹' (U : Set G) := by
      simp [U.one_mem]
    filter_upwards [hop.mem_nhds hx] with y hy
    have h1 := h (x⁻¹ * y) hy x
    simpa using h1
  exact continuousAt_const.congr hev.symm

private theorem cptPart_le {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) :
    GlobalTheory.BCT.cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ ht => ht.1

theorem orbSum : OrbSum := by
  unfold OrbSum
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 θ hθ δ T hT hcomm hC ν hν U f hU hf hcm
  subst hT
  obtain ⟨hUo, hUK, hUθ⟩ := hU
  obtain ⟨hfc, hfi⟩ := hf
  set F : G → ℂ := fun x => f (x⁻¹ * δ * θ x) with hF
  have hTcl : IsClosed (GlobalTheory.BCT.twCent θ δ : Set G) := by
    show IsClosed {g : G | g * δ = δ * θ g}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hFU : ∀ u ∈ U, ∀ x : G, F (x * u) = F x := by
    intro u hu x
    show f ((x * u)⁻¹ * δ * θ (x * u)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    have h1 : θ u ∈ U := hUθ u hu
    have hu' : u⁻¹ ∈ U := U.inv_mem hu
    calc f (u⁻¹ * x⁻¹ * δ * (θ x * θ u)) = f (u⁻¹ * (x⁻¹ * δ * θ x) * θ u) := by
          simp only [mul_assoc]
      _ = f (u⁻¹ * (x⁻¹ * δ * θ x)) := (hfi _ h1 _).2
      _ = f (x⁻¹ * δ * θ x) := (hfi _ hu' _).1
  have hFT : ∀ t ∈ GlobalTheory.BCT.twCent θ δ, ∀ x : G, F (t * x) = F x := by
    intro t ht x
    have h : t * δ = δ * θ t := ht
    have h2 : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← h, inv_mul_cancel_left]
    show f ((t * x)⁻¹ * δ * θ (t * x)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    calc f (x⁻¹ * t⁻¹ * δ * (θ t * θ x)) = f (x⁻¹ * (t⁻¹ * δ * θ t) * θ x) := by
          simp only [mul_assoc]
      _ = f (x⁻¹ * δ * θ x) := by rw [h2]
  have hFc : Continuous F := continuous_of_rightInv U hUo F hFU
  obtain ⟨_, hsum⟩ := sumCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT hcm
  have hmapK : ∀ q x : G, x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K ↔
      q⁻¹ * x * q ∈ K := by
    intro q x
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro hx
      exact ⟨q⁻¹ * x * q, hx, by simp [mul_assoc]⟩
  have hset : ∀ q : G, {t : GlobalTheory.BCT.twCent θ δ | q⁻¹ * (t : G) * q ∈ K} =
      {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    ext t
    simp only [Set.mem_setOf_eq, Subgroup.mem_inf, hmapK, SetLike.coe_mem, true_and]
  have hopen : ∀ q : G, IsOpen {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    rw [← hset q]
    exact hKo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hvol : ∀ q : G, _ := fun q => volIdx G (GlobalTheory.BCT.twCent θ δ) (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ))
    (GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K) hTcl ν hν
    (cptPart_le _) hC
    (GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc q)) (hopen q)
  have hCfin : ν {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ ⊤ :=
    ((hTcl.isClosedEmbedding_subtypeVal).isCompact_preimage hC).measure_lt_top.ne
  have hCne : ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ 0 := by
    have h1 := (hvol 1).1
    have hsub : {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : G))) K} ⊆
        {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} :=
      fun t ht => GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc 1) ht
    have h2 := measureReal_mono hsub hCfin
    intro h0
    exact h1 (le_antisymm (h0 ▸ h2) measureReal_nonneg)
  refine ⟨hCne, ?_⟩
  rw [hsum]
  unfold GlobalTheory.BCT.twOrb
  rw [mul_finsum]
  refine finsum_congr fun q => ?_
  obtain ⟨hH0, hCeq⟩ := hvol (Quotient.out q)
  have hidx : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℝ) ≠ 0 := fun h0 => hCne (by rw [hCeq, h0, zero_mul])
  rw [oneCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT (Quotient.out q)]
  rw [← avgInt G μ hμ K hKo hKc hK1 U hUo F hFU (Quotient.out q)]
  rw [hset, hCeq]
  rw [show (fun y : K => F (Quotient.out q * ↑y)) =
    fun k : K => f ((Quotient.out q * ↑k)⁻¹ * δ * θ (Quotient.out q * ↑k)) from rfl]
  have hidxC : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hHC : ((ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K} : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hH0
  push_cast
  field_simp

end UpperTheory.Gal.InertialTypesAlt.L
end
end
end
