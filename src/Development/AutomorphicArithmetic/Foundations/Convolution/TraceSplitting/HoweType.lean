module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.GalIsom
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.PsiInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceData
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweLine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxSubsetOfMemNhdsZero

section

@[expose] public section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.NearOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_valuation_sub_lt_one (a : k) : ∀ᶠ x in nhds a, valuation k (x - a) < 1 := by
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨1, one_ne_zero, subset_rfl⟩
  have hc : Filter.Tendsto (fun x : k => x - a) (nhds a) (nhds 0) := by
    have : Continuous (fun x : k => x - a) := by fun_prop
    simpa using this.tendsto a
  exact hc h0

theorem exists_box_subset_of_mem_nhds_zero {p q : ℕ} {S : Set (Matrix (Fin p) (Fin q) k)} (hS : S ∈ nhds 0) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ box p q d ⊆ S := by
  have hk : ∀ s ∈ nhds (0 : k), ∀ᶠ d in nhds (0 : k), {x : k | valuation k x ≤ valuation k d} ⊆ s := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
    have h0 : {x : k | valuation k x < r} ∈ nhds (0 : k) :=
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨r, hr, subset_rfl⟩
    filter_upwards [h0] with d hd x hx
    exact hrs (lt_of_le_of_lt hx hd)
  have hS' : {x : Fin p → Fin q → k | Matrix.of x ∈ S} ∈ nhds (0 : Fin p → Fin q → k) := hS
  rw [nhds_pi, Filter.mem_pi'] at hS'
  obtain ⟨I, t, ht, hI⟩ := hS'
  have ht' : ∀ i, ∃ u : Fin q → Set k, (∀ j, u j ∈ nhds (0 : k)) ∧ Set.univ.pi u ⊆ t i := by
    intro i
    have h := ht i
    rw [nhds_pi, Filter.mem_pi'] at h
    obtain ⟨J, u, hu, hJ⟩ := h
    exact ⟨u, hu, fun x hx => hJ fun j _ => hx j trivial⟩
  choose u hu hut using ht'
  have hev : ∀ᶠ d in nhds (0 : k), valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j :=
    (eventually_valuation_sub_lt_one 0).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hk _ (hu i j))
  have hne : ∃ d : k, d ≠ 0 ∧ valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j := by
    have hd : (nhdsWithin (0 : k) {0}ᶜ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
      intro s hs
      obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
      obtain ⟨r', hr', hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
      obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective r
      have hy : y ≠ 0 := by simpa using hr
      refine ⟨r' * y, hrs ?_, mul_ne_zero (by simpa using hr') hy⟩
      show valuation k (r' * y) < valuation k y
      rw [map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.mpr hr) hr1
    exact (eventually_mem_nhdsWithin.and (hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)))).exists
  obtain ⟨d, hd0, hd1, hdu⟩ := hne
  refine ⟨Units.mk0 d hd0, by simpa using hd1.le, fun X hX => hI fun i _ => hut i fun j _ => hdu i j (hX i j)⟩

theorem one_add_small_near_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ ∀ N ∈ box n n d, ∃ A : GL (Fin n) k, A.val = 1 + N ∧ A ∈ U ∧
      valuation k (GeneralLinearGroup.det A : k) = 1 ∧ A⁻¹.val ∈ box n n 1 := by
  have hadd : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => 1 + N) (nhds 0) (nhds 1) := by
    have : Continuous (fun N : Matrix (Fin n) (Fin n) k => 1 + N) := by fun_prop
    simpa using this.tendsto 0
  have hdet : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N).det) (nhds 0) (nhds 1) := by
    have : Continuous (fun M : Matrix (Fin n) (Fin n) k => M.det) := continuous_id.matrix_det
    have h2 := (this.tendsto 1).comp hadd
    rw [det_one] at h2
    exact h2
  have hinv : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N)⁻¹) (nhds 0) (nhds 1) := by
    have : ContinuousAt Inv.inv (1 : Matrix (Fin n) (Fin n) k) := by
      apply continuousAt_matrix_inv
      rw [det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h2 := this.tendsto.comp hadd
    rw [inv_one] at h2
    exact h2
  have hv : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, valuation k (1 + N).det = 1 := by
    filter_upwards [hdet (eventually_valuation_sub_lt_one 1)] with N hN
    have hN' : valuation k ((1 + N).det - 1) < 1 := hN
    have := Valuation.map_one_add_of_lt (valuation k) hN'
    simpa using this
  have hb : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, ∀ i j, valuation k ((1 + N)⁻¹ i j) ≤ 1 := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have hc : Continuous (fun M : Matrix (Fin n) (Fin n) k => M i j) := continuous_id.matrix_elem i j
    filter_upwards [((hc.tendsto 1).comp hinv) (eventually_valuation_sub_lt_one _)] with N hN
    have hN' : valuation k ((1 + N)⁻¹ i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := hN
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have := Valuation.map_add_le (valuation k) hN'.le h1
    simpa using this
  have hval : ∀ N : Matrix (Fin n) (Fin n) k, valuation k (1 + N).det = 1 → (toGL (1 + N)).val = 1 + N := by
    intro N hN
    have hu : IsUnit (1 + N) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h
      rw [h] at hN
      simp at hN
    unfold toGL
    rw [dite_eq_left hu]
    rfl
  have hGL : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => toGL (1 + N)) (nhds 0) (nhds 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have h3 := hadd.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp hinv)
    have e : (Units.embedProduct _ (1 : GL (Fin n) k)) = (1, MulOpposite.op 1) := by simp
    rw [e]
    refine Filter.Tendsto.congr' ?_ h3
    filter_upwards [hv] with N hN
    simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, hval N hN]
  obtain ⟨d, hd, hS⟩ := exists_box_subset_of_mem_nhds_zero (p := n) (q := n) (hv.and (hb.and (hGL hU)))
  refine ⟨d, hd, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS hN
  refine ⟨toGL (1 + N), hval N h1, h3, ?_, fun i j => ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, hval N h1, h1]
  · rw [Matrix.coe_units_inv, hval N h1]
    simpa using h2 i j

end GlobalTheory.GamMul.NearOne
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweBall

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.howeBall :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (c : ℤ) (ρ : ValueGroupWithZero E), 0 < ρ →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSet n ϖ a c ⊆ ball n ρ := by
  intro E _ _ _ _ n ϖ hϖ c ρ hρ
  have h1 : valuation E (ϖ : E) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have h0 : 0 < valuation E (ϖ : E) := by rw [hϖ]; exact uniformizer_pos
  haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 ρ hρ.ne')
  refine ⟨N + |c| * n, fun a ha g hg i j => (hg i j).trans ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  refine le_trans ?_ hN.le
  rw [← zpow_natCast]
  refine zpow_le_zpow_right_of_le_one₀ h0 h1.le ?_
  have hi := i.2
  have hj := j.2
  have h2 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ n := by
    rw [abs_le]; constructor <;> omega
  have h3 : |c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))| ≤ |c| * n := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h4 := (abs_le.1 h3).1
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.HoweType

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

private theorem ball_sub_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (N : Set (GL (Fin n) k)) (hN : N ∈ nhds (1 : GL (Fin n) k)) :
    ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ball n ρ ⊆ N := by
  obtain ⟨d, -, h⟩ := GlobalTheory.GamMul.NearOne.one_add_small_near_one k n N hN
  refine ⟨valuation k (d : k), ?_, fun g hg => ?_⟩
  · exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 d.ne_zero)
  · obtain ⟨A, hA, hAN, -⟩ := h ((g : Matrix (Fin n) (Fin n) k) - 1) (fun i j => hg i j)
    have e : A = g := Units.ext (by rw [hA]; simp)
    exact e ▸ hAN

private theorem local_type (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E)
    (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) E) W) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hg : GlobalTheory.LocGL.IsGeneric π) (N : Set (GL (Fin n) E)) (hN : N ∈ nhds (1 : GL (Fin n) E)) :
    ∃ (J : Subgroup (GL (Fin n) E)) (χ : GL (Fin n) E → ℂ) (e : W), CO J ∧ IsChr J χ ∧ (J : Set (GL (Fin n) E)) ⊆ N ∧
      e ≠ 0 ∧ (∀ g ∈ J, π g e = χ g • e) ∧ (∀ x : W, (∀ g ∈ J, π g x = χ g • x) → ∃ c : ℂ, x = c • e) ∧
      ∀ y ∈ J, Matrix.GeneralLinearGroup.map (s : E →+* E) y ∈ J ∧
        χ (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = χ y := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := E) (uniformizer E)
    exact ⟨Units.mk0 x fun h => uniformizer_ne_zero (R := E) (by rw [← hx, h, map_zero]), hx⟩
  obtain ⟨ρ, hρ, hρN⟩ := ball_sub_nhds E n N hN
  obtain ⟨c, hc⟩ := psiInv k E ϖ hϖ
  obtain ⟨a₁, h₁⟩ := howeLine E n W π hs hi hg ϖ hϖ c
  obtain ⟨a₂, h₂⟩ := howeBall E n ϖ hϖ c ρ hρ
  obtain ⟨a, ha, ψ, hψ, hinv⟩ := hc (max 1 (max a₁ a₂))
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  obtain ⟨J, hJ, ho, hk⟩ := howeGroup E n ϖ hϖ a c ha1
  obtain ⟨hlc, hmul⟩ := howeChar E n ϖ hϖ a c ha1 ψ hψ
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  have hline := h₁ a (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha) ψ hψ
  obtain ⟨⟨e, he⟩, he0, hspan⟩ := finrank_eq_one_iff'.1 hline
  refine ⟨J, fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ), e, ⟨hk, ho⟩, ⟨hlc, fun x _ => Circle.norm_coe _, fun x hx y hy => ?_⟩, ?_,
    fun h => he0 (Subtype.ext h), fun g hgJ => he g ((hmem g).1 hgJ), fun x hx => ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]
  · rw [hJ]
    exact (h₂ a (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha)).trans hρN
  · obtain ⟨t, ht⟩ := hspan ⟨x, fun g hg => hx g ((hmem g).2 hg)⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  · have hy' := (hmem y).1 hy
    have hent : ∀ i j, ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
        s ((y : Matrix (Fin n) (Fin n) E) i j) := fun _ _ => rfl
    refine ⟨(hmem _).2 fun i j => ?_, ?_⟩
    · have e1 : ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j -
          (1 : Matrix (Fin n) (Fin n) E) i j = s ((y : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [hent, map_sub, Matrix.one_apply, apply_ite s, map_one, map_zero]
      rw [e1, galIsom k E]
      exact hy' i j
    · have hsd : GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = s (GlobalTheory.Whittaker.superDiag y) := by

        simp only [GlobalTheory.Whittaker.superDiag, map_sum, hent]
      change ((ψ (GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y)) : Circle) : ℂ) = _
      rw [hsd, hinv]

theorem UpperTheory.ConvolutionTheory.T.howeType :
    UpperTheory.ConvolutionTheory.T.HoweType := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ μ _ V hV v w hw N hN
  obtain ⟨iA, iV, iFD, iG, s, -, -, -, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨π, hπ, -⟩ : ∃! π : GlobalTheory.CuspRep.CuspSub E n,
      UpperTheory.ConvolutionTheory.Dp.Carries μ π V :=
    UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV
  obtain ⟨hl, -, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n
  letI : MeasurableSpace (Gw n w.1) := borel _
  haveI : BorelSpace (Gw n w.1) := ⟨rfl⟩
  obtain ⟨⟨τ, hτ⟩, -, -⟩ := occursBasics E n μ V w.1 MeasureTheory.Measure.haar hV
  have hloc : (UpperTheory.CBC.Cusp.cx π).locComp w.1 τ :=
    (UpperTheory.ConvolutionTheory.Dp.locIff E n μ π V hπ w.1 τ).2 ((occursIff E n μ V hV w.1 τ).1 hτ)
  have hgen : GlobalTheory.LocGL.IsGeneric τ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w.1 τ hloc
  obtain ⟨J, χ, e, hCO, hchr, hJN, he0, heJ, hline, hst⟩ :=
    local_type (v.adicCompletion F) (w.1.adicCompletion E) s n τ.V τ.ρ τ.smooth τ.irred hgen N hN
  have hrank := lineRank E n μ V hV w.1 τ hτ J χ hCO hchr ⟨e, hline⟩
  obtain ⟨f, hf0, hfV, hfe⟩ := hτ
  have hinj : Function.Injective f := by
    let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hfe, hx, map_zero]⟩
    haveI := τ.irred
    rcases eq_bot_or_eq_top K with h | h
    · refine LinearMap.ker_eq_bot.1 ?_
      exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hf0
      have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_top.1 h'
  refine ⟨J, χ, hCO, hchr, hJN, hrank, fun h => ?_, fun x hx => ?_⟩
  · have hm : f e ∈ V ⊓ eigL μ w.1 J χ := by
      refine ⟨hfV e, ?_⟩
      simp only [eigL, SetLike.mem_coe, Submodule.mem_iInf]
      intro x hx
      change rhoL μ w.1 x (f e) = χ x • f e
      rw [← hfe, heJ x hx, map_smul]
    rw [h, Submodule.mem_bot] at hm
    exact he0 (hinj (by rw [hm, map_zero]))
  · have hcm : UpperTheory.ConvolutionTheory.GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.galFin σ v) x) =
        Matrix.GeneralLinearGroup.map (s : w.1.adicCompletion E →+* w.1.adicCompletion E) (UpperTheory.ConvolutionTheory.GM.cmp w x) :=
      Units.ext (Matrix.ext fun i j => hgal _)
    rw [hcm]
    exact hst _ hx
end
end
