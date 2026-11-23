module

public import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Mathlib.RingTheory.Valuation.AlgebraInstances
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristic
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValueStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Mathlib.RingTheory.Valuation.LocalSubring

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristicStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cuspForm_integral_values_equal_characteristic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.EqCharCusp.integral_of_eqChar | exact GlobalTheory.EqCharCusp.integral_of_eqChar | (intros; apply GlobalTheory.EqCharCusp.integral_of_eqChar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralAdjoinOfForallCdvr

section

@[expose] public section

open Formalism.L2.Pj

open IsLocalRing

namespace GlobalTheory

theorem isIntegral_adjoin_of_forall_cdvr (K Ω : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (gens : Finset Ω)
    (hcl : Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤) (x : Ω)
    (hx : ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr,
      (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) →
      (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) :
    IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  classical
  set A := Algebra.adjoin K (gens : Set Ω) with hAdef

  have hfrac : ∀ z : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ z * b = a := by
    intro z
    have hz : z ∈ Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) := hcl ▸ trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
    have hc : Subring.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = A.toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm
    rw [hc] at ha hb
    rcases eq_or_ne b 0 with rfl | hb0
    · exact ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, by simp⟩
    · exact ⟨a, ha, b, hb, hb0, div_mul_cancel₀ a hb0⟩

  have hKc : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have hΩc : Countable Ω := by
    have hs : (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)).Countable :=
      (Set.countable_range _).union gens.finite_toSet.countable
    have h1 : Cardinal.mk (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))) ≤
        Cardinal.aleph0 :=
      (Subfield.cardinalMk_closure_le_max _).trans
        (max_le (Cardinal.mk_le_aleph0_iff.2 hs.to_subtype) le_rfl)
    have h2 := Cardinal.mk_le_aleph0_iff.1 h1
    rw [hcl] at h2
    exact Function.Injective.countable (f := fun (z : Ω) => (⟨z, trivial⟩ : (⊤ : Subfield Ω)))
      fun a b h => congrArg Subtype.val h

  have hAft : Algebra.FiniteType K A := .adjoin_of_finite gens.finite_toSet
  have hAn : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hess : Algebra.EssFiniteType A Ω := by
    refine (Algebra.essFiniteType_iff A Ω).mpr ⟨∅, fun z => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hfrac z
    simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot]
    exact ⟨b, ⟨⟨b, hb⟩, rfl⟩, isUnit_iff_ne_zero.mpr hb0, ⟨⟨a, ha⟩, hab.symm⟩⟩
  by_contra hni
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hni isIntegral_zero

  letI := invertibleOfNonzero (inv_ne_zero hx0)
  let B := Algebra.adjoin A {x⁻¹}
  let xinv : B := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have hne : (⊥ : Ideal A).map (algebraMap A B) ⊔ Ideal.span {xinv} ≠ ⊤ := by
    intro heq
    obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
      x⁻¹ (⊥ : Ideal A) bot_ne_top heq
    have hm : p.Monic := by
      rw [Ideal.mem_bot, sub_eq_zero] at hp
      exact hp
    rw [invOf_eq_inv, inv_inv] at hpx
    exact hni ⟨p, hm, by rw [← Polynomial.aeval_def, hpx]⟩
  obtain ⟨W, hW, hW'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ hne
  have hxW : x⁻¹ ∈ W.nonunits := hW' ⟨xinv, Ideal.mem_sup_right (Ideal.subset_span rfl), rfl⟩

  obtain ⟨V, hV, hAV, -, hxV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := A)
    W (fun r => hW (B.algebraMap_mem r)) (s := ∅) (t := {x⁻¹}) Set.finite_empty
    (Set.finite_singleton _) (by simp) (by simpa using hxW) ⟨x⁻¹, rfl, inv_ne_zero hx0⟩
  have hxV' : x⁻¹ ∈ V.nonunits := hxV _ rfl
  have hKV : ∀ k : K, algebraMap K Ω k ∈ V := fun k => hAV (algebraMap K A k)
  have hgV : ∀ g ∈ gens, g ∈ V := fun g hg => hAV ⟨g, Algebra.subset_adjoin hg⟩

  let ι := algebraMap V (AdicCompletion (maximalIdeal V) V)
  have hch : CharZero (AdicCompletion (maximalIdeal V) V) :=
    (RingHom.charZero_iff (ι.comp ((algebraMap K Ω).codRestrict V hKV)).injective).1 inferInstance
  let T : CDVR := { V := AdicCompletion (maximalIdeal V) V, ch0 := hch }
  have hVc : Countable V := Subtype.countable
  have hres : Countable (ResidueField T.V) := by
    have hsurj : Function.Surjective ((residue T.V).comp ι) := by
      intro t0
      obtain ⟨t, rfl⟩ := residue_surjective t0
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (maximalIdeal V) 1 t)
      refine ⟨r, ?_⟩
      change residue T.V (ι r) = residue T.V t
      change Ideal.Quotient.mk _ (ι r) = Ideal.Quotient.mk _ t
      rw [Ideal.Quotient.eq]
      intro hu
      have hnt : Nontrivial (V ⧸ maximalIdeal V ^ 1) := by
        rw [pow_one]; infer_instance
      have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal V) 1)
      rw [map_sub] at h1
      change IsUnit ((AdicCompletion.evalₐ (maximalIdeal V) 1) (AdicCompletion.of _ _ r) - _) at h1
      rw [AdicCompletion.evalₐ_of, hr, sub_self] at h1
      exact not_isUnit_zero h1
    exact hsurj.countable
  have hg : Function.Injective ((algebraMap T.V T.Fr).comp ι) :=
    (IsFractionRing.injective T.V T.Fr).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let φ : Ω →+* T.Fr := IsFractionRing.lift (A := V) hg
  have hφ : ∀ v : V, φ v = algebraMap T.V T.Fr (ι v) := fun v => IsFractionRing.lift_algebraMap hg v
  obtain ⟨t, ht⟩ := hx T hres φ (fun k => ⟨ι ⟨_, hKV k⟩, (hφ ⟨_, hKV k⟩).symm⟩)
    (fun g hg' => ⟨ι ⟨g, hgV g hg'⟩, (hφ ⟨g, hgV g hg'⟩).symm⟩)
  let y : V := ⟨x⁻¹, V.nonunits_subset hxV'⟩
  have h1 : algebraMap T.V T.Fr (t * ι y) = 1 := by
    rw [map_mul, ht, ← hφ y]
    change φ x * φ x⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  have h2 : t * ι y = 1 := IsFractionRing.injective T.V T.Fr (h1.trans (map_one _).symm)
  have h3 : IsUnit (ι y) := isUnit_iff_exists_inv.mpr ⟨t, by rw [mul_comm]; exact h2⟩
  exact (ValuationSubring.coe_mem_nonunits_iff (a := y)).mp hxV' (isUnit_of_map_unit ι y h3)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralAdjoinOfForallCdvrStatement

section

@[expose] public section

open Formalism.L2.Pj

theorem _root_.GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (gens : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → ∀ x : Ω, (∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr, (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) → (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) → IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  first | exact @GlobalTheory.isIntegral_adjoin_of_forall_cdvr | exact GlobalTheory.isIntegral_adjoin_of_forall_cdvr | (intros; apply GlobalTheory.isIntegral_adjoin_of_forall_cdvr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPole

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspReg

theorem exists_cover_noPole : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ (J : Type) (_ : Finite J) (P : J → GlobalTheory.Reg.PChart Xo c (algebraMap (la.valuation c.F).valuationSubring c.F)), GlobalTheory.Reg.Covers P ∧ ∀ j, evR Xo c f (P j).yg ∈ Algebra.adjoin c.F ((P j).gens : Set (P j).Ω) := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hF := cusp_le_sec Xo c U a n hf
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
  have hY : ∃ Y : Model Xo c (algebraMap (la.valuation c.F).valuationSubring c.F),
      PushInvertible Y.t.G Y.t.PP.L := by
    by_cases hr : 1 ≤ Dw.p + Dw.q
    · obtain ⟨Y, hP, -⟩ := GlobalTheory.GoodTransfer.exists_model hr Xo c la p hp hpl hg
      exact ⟨Y, hP⟩
    · exact GlobalTheory.SupFinite.exists_model_rank_zero (Xo := Xo) (c := c) (by omega) _
  obtain ⟨Y, hP⟩ := hY
  obtain ⟨J, hJ, P, hC⟩ := GlobalTheory.Reg.exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c
    hE.bc (la.valuation c.F).valuationSubring Y hP
  set_option synthInstance.maxHeartbeats 200000 in
  have hmem : ∀ j, ∀ e ∈ (P j).es, evR Xo c f (P j).yg ∈ (P j).R e := fun j e he => by
    rw [(hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)]
    exact (evR Xo c f ((P j).y e he)).2
  have hint : ∀ j, IsIntegral (Algebra.adjoin c.F ((P j).gens : Set (P j).Ω)) (evR Xo c f (P j).yg) := by
    intro j
    refine GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem c.F (P j).Ω (P j).gens (P j).frac _ fun T hT φ hK hgn => ?_
    obtain ⟨e, he⟩ := (P j).es_ne
    let io : c.F →+* T.Fr := φ.comp (algebraMap c.F (P j).Ω)
    letI := io.toAlgebra
    let ψ : (P j).R e →ₐ[c.F] T.Fr :=
      { toRingHom := φ.comp ((P j).R e).val.toRingHom, commutes' := fun k => rfl }
    obtain ⟨z, hz⟩ := hE.bc _ _ ψ ((P j).y e he)
    have hzI := (P j).int e he T io ψ (fun a => hK _) (fun g hg' => hgn _ hg') z hz
    have h1 := GlobalTheory.T.cuspForm_integral_values_equal_characteristic E H Dw l Xo c r U hU a n f hd hf T hT io hK ⟨z, hE.test _ z, hzI⟩
    have e1 : evR Xo c f z = ψ (evR Xo c f ((P j).y e he)) := (hev _).1 _ ψ _ _ hz
    have e2 : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
      (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
    rw [e2]
    change evR Xo c f z ∈ _ at h1
    rw [e1] at h1
    exact h1
  choose P' hP'1 hP'2 using fun j => GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value E H Dw l Xo c (la.valuation c.F).valuationSubring f (P j) (hmem j) (hint j)
  refine ⟨J, hJ, P', fun L _ _ W hW y => ?_, hP'1⟩
  obtain ⟨j, hj⟩ := hC L W hW y
  exact ⟨j, hP'2 j L W hW y hj⟩

end GlobalTheory.CuspReg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPoleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_integral_chart_cover_cuspForm_no_pole : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ (J : Type) (_ : Finite J) (P : J → GlobalTheory.Reg.PChart Xo c (algebraMap (la.valuation c.F).valuationSubring c.F)), GlobalTheory.Reg.Covers P ∧ ∀ j, evR Xo c f (P j).yg ∈ Algebra.adjoin c.F ((P j).gens : Set (P j).Ω) := by
  first | exact @GlobalTheory.CuspReg.exists_cover_noPole | exact GlobalTheory.CuspReg.exists_cover_noPole | (intros; apply GlobalTheory.CuspReg.exists_cover_noPole <;> assumption)
end
end
