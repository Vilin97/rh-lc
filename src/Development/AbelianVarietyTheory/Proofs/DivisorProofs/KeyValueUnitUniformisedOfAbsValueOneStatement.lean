module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HvHolds
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
public import Mathlib.SetTheory.Cardinal.Continuum
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Cardinality
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametricStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroFibresUnitMultipleThetaSeriesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormNatEqOne

section

@[expose] public section

open Cardinal
namespace GlobalTheory.MomOne.Inh

theorem mk_le {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

theorem nonempty_iso (p : ℕ) [Fact p.Prime] : Nonempty (ℂ ≃+* ℂ_[p]) := by
  have h1 : #ℚ_[p] ≤ 𝔠 := mk_le _ (Padic.denseRange_ratCast p)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have h2 : #(PadicAlgCl p) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le h1 Cardinal.aleph0_le_continuum)
  have h3 : #(ℂ_[p]) ≤ 𝔠 := mk_le (X := PadicComplex p) _
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) h2
  have h4 : 𝔠 ≤ #(ℂ_[p]) := continuum_le_cardinal_of_nontriviallyNormedField _
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) ?_
  exact Cardinal.eq.1 (by rw [Cardinal.mk_complex]; exact le_antisymm h4 h3)

end GlobalTheory.MomOne.Inh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteAlgClosedFieldDvrEmbedding

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CompleteDvrToComplex

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ IsLocalRing.maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem norm_le_one_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl),
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

theorem norm_natCast_prime_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have hc : ((p : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by push_cast; rfl
  rw [hc] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem exists_complete_closed_field :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  intro V _ _ _ _ hc hf
  let T : Formalism.L2.Pj.CDVR := { V := V }
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hf
  letI : Algebra (FractionRing V) ℂ_[p] := k.toAlgebra
  obtain ⟨eC⟩ := GlobalTheory.MomOne.Inh.nonempty_iso p
  refine ⟨ℂ_[p], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ⟨?_, ?_⟩, ⟨eC.symm⟩⟩
  · have hle : ∀ r : V, ‖k (algebraMap V (FractionRing V) r)‖ ≤ 1 := fun r => by
      rw [← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    exact hle
  · have hle : ∀ r : V, ‖(k.comp (algebraMap V (FractionRing V))) r‖ ≤ 1 := fun r => by
      rw [RingHom.comp_apply, ← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have hpl : ‖(k.comp (algebraMap V (FractionRing V))) (p : V)‖ < 1 := by
      rw [map_natCast]; exact norm_natCast_prime_lt_one p
    intro r hr
    exact norm_lt_one_of_mem_maximalIdeal _ hle hp0 hpl hr

end GlobalTheory.CompleteDvrToComplex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteAlgClosedFieldDvrEmbeddingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_dvr_embedding : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  first | exact @GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field | exact GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field | (intros; apply GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyTraitU_of_kapF : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  intro κ hK V _ _ _ _ hcpl hfin D x G _ _ hG U w₀ hN y hy hvec σ hNz hMaps
  obtain ⟨C, i1, i2, i3, i4, i5, i6, hC, hCC⟩ := GlobalTheory.T.exists_complete_algClosed_field_dvr_embedding V hcpl hfin
  obtain ⟨N, ν, hInt⟩ := GlobalTheory.T.exists_degenerationData_values_ultrametric V hcpl D C hC
  obtain ⟨σ₁, f, th, ϑ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.integralSection_expands_integrally_genericFibre V hcpl D x.P G hG U w₀ hN.1 x.th σ hMaps C
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  obtain ⟨hv₁, -, -, -, hv₅, -⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨f', hf', -⟩ := hv₁ ϑ
  obtain ⟨c, rfl⟩ := hv₅ ϑ f' hf'
  have hc : ‖c‖ = 1 := GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries V hcpl D x.P G hG U σ σ₁ f hNz h1 h2 C hC N ν hInt ϑ c h5 hf'
  have e := hK V hcpl hfin D x G hG U w₀ hN y hy hvec C hC hCC N ν hInt th ϑ c h3 h4 hf'
  rw [hc, one_pow, _root_.one_mul] at e
  exact GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr V C hC _ e

end GlobalTheory.KeyEven
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyValue_unit_uniformised_of_absValueOne : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  first | exact @GlobalTheory.KeyEven.keyTraitU_of_kapF | exact GlobalTheory.KeyEven.keyTraitU_of_kapF | (intros; apply GlobalTheory.KeyEven.keyTraitU_of_kapF <;> assumption)
end
end
