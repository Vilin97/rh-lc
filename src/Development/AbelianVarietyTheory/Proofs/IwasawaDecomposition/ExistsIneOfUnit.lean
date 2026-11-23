module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyAndNormOfPowEqUniformizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlacStatement
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitPowNormVSubOneStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusInvMulMemInertiaStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRatioPiCongrTameUnitStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMemStatement
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisenstein

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRecip

theorem exists_frob_fix_of_eisenstein : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  intro hG E Ω _ _ _ _ _ _ art hart v A hA ϖ hϖ hϖ2 π hπ
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional E (IntermediateField.adjoin E {π}) := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField (IntermediateField.adjoin E {π}) := NumberField.of_module_finite E _
  have : IsAlgClosure (IntermediateField.adjoin E {π}) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  set K := IntermediateField.adjoin E {π} with hKdef
  obtain ⟨artK, hartK⟩ := hG K Ω
  obtain ⟨W, hWv, hWuniq, hAW, hnW, hunif⟩ := GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place E Ω v A hA ϖ hϖ hϖ2 π hπ
  obtain ⟨-, hnorm⟩ := GlobalTheory.TameEis.minpoly_and_norm_of_pow_eq_uniformizer E Ω v ϖ hϖ hϖ2 π hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have hv1 : (1 : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rcases Nat.eq_zero_or_pos (normV v - 1) with h0 | h0
    · rw [h0, pow_zero] at hπ
      have : (ϖ : E) = ((1 : 𝓞 E) : E) := by
        apply (algebraMap E Ω).injective; rw [← hπ]; simp
      exact hv1 (by rw [← (RingOfIntegers.coe_injective this)]; exact hϖ)
    · rw [zero_pow h0.ne'] at hπ
      have : (ϖ : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hπ.symm
      exact hϖ2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.mp this]; exact Ideal.zero_mem _)
  have hgen0 : IntermediateField.AdjoinSimple.gen E π ≠ 0 := by
    intro h; apply hπ0
    have := congrArg (algebraMap K Ω) h
    simpa using this
  set yK : Kˣ := Units.mk0 _ hgen0 with hyK
  set cπ : (W.adicCompletion K)ˣ := Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom yK with hcπ
  have hcu : IsUnifAt W cπ := hunif cπ rfl
  obtain ⟨σ, hσF, hσA⟩ := (hartK.frob W A hAW (artK (localIdele K W cπ))).mp ⟨cπ, hcu, rfl⟩
  have hN := GlobalTheory.T.artin_restrict_eq_artin_norm_single_place E Ω K art artK hart hartK v W hWv hWuniq yK σ⁻¹ hσA
  refine ⟨σ.restrictScalars E, ?_, ?_, ?_⟩
  · rw [← hnW]; exact hσF
  · have := σ.commutes (IntermediateField.AdjoinSimple.gen E π)
    simpa using this
  · intro c hc
    have hinv : (σ.restrictScalars E)⁻¹ = (σ⁻¹).restrictScalars E := rfl
    rw [hinv, hN]
    congr 2
    ext
    rw [hc]
    simp only [Units.coe_map, MonoidHom.coe_coe, hyK, Units.val_mk0]
    rw [hnorm]
    simp

end GlobalTheory.TameRecip
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisensteinStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_frob_of_eisenstein_root : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  exact @GlobalTheory.TameRecip.exists_frob_fix_of_eisenstein
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem GlobalTheory.TameRecip.exists_ine_of_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) → ∀ (x : (v.adicCompletion E)ˣ) (u : 𝓞 E), IsUnitAt v x → Valued.v ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) < 1 → ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = art (localIdele E v x) ∧ A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 := by
  intro H E Ω _ _ _ _ _ _ art ha v A hA ϖ hϖ1 hϖ2 π hπ x u hx hxu
  have hq : 1 < normV v := by
    unfold normV
    have : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    exact Finite.one_lt_card
  have hn : 0 < normV v - 1 := by omega
  have hvE : ∀ a : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (a : E)) = v.valuation E (a : E) :=
    fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hu1 : Valued.v (algebraMap E (v.adicCompletion E) (u : E)) = 1 := by
    rw [hvE]
    refine le_antisymm (v.valuation_le_one u) (not_lt.mp fun h => ?_)
    have hm : u ∈ v.asIdeal := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mp h
    have hlt : Valued.v (x : v.adicCompletion E) < 1 := by
      have e : (x : v.adicCompletion E) = ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) +
          algebraMap E (v.adicCompletion E) (u : E) := by ring
      rw [e]
      refine Valuation.map_add_lt _ hxu ?_
      rw [hvE]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
    rw [hx'] at hlt
    exact lt_irrefl _ hlt
  have hu : u ∉ v.asIdeal := by
    intro hm
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    rw [← hvE, hu1] at h
    exact lt_irrefl _ h
  have hu0 : algebraMap E (v.adicCompletion E) (u : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  let uc : (v.adicCompletion E)ˣ := Units.mk0 _ hu0
  have hy : Valued.v (((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) < 1 := by
    have e : ((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
        ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) *
          (algebraMap E (v.adicCompletion E) (u : E))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, uc, Units.val_mk0]
      field_simp
    rw [e, map_mul, map_inv₀, hu1, inv_one, mul_one]
    exact hxu
  obtain ⟨z, hz1, hz⟩ := GlobalTheory.T.exists_unit_pow_normV_sub_one' E v (x * uc⁻¹) hy
  obtain ⟨ρ, hρ, hρz⟩ := (ha.ine v A hA _).mp ⟨z, hz1, rfl⟩
  obtain ⟨τ, hτF, hτπ, hτc⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA ϖ hϖ1 hϖ2 π hπ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E)) hn
  have h1' : u * ϖ ∈ v.asIdeal := Ideal.mul_mem_left _ _ hϖ1
  have h2' : u * ϖ ∉ v.asIdeal ^ 2 := by
    intro h
    rcases Ideal.IsPrime.mul_mem_pow v.asIdeal h with h3 | h3
    · exact hu h3
    · exact hϖ2 h3
  have hπ' : (π * t) ^ (normV v - 1) = algebraMap E Ω ((u * ϖ : 𝓞 E) : E) := by
    rw [mul_pow, hπ, ht, ← map_mul]
    push_cast
    ring_nf
  obtain ⟨τ', hτ'F, hτ'π, hτ'c⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA (u * ϖ) h1' h2' (π * t) hπ'
  have hσ0 : τ'⁻¹ * τ ∈ Ine (F := E) A := GlobalTheory.T.frobenius_inv_mul_mem_inertia E Ω v A hA τ τ' hτF hτ'F
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 hπ
  have hval := GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit E Ω v A hA u hu π t hπ0 ht τ τ' hτF hτ'F hτπ hτ'π
  have hc0 : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ((map_ne_zero _).mpr hϖ0)
  have huE : (u : E) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hcast : ((u * ϖ : 𝓞 E) : E) = (u : E) * (ϖ : E) := by push_cast; ring
  have hs0 : ((-1) ^ normV v : v.adicCompletion E) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hϖc : algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hc0' : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (((u * ϖ : 𝓞 E)) : E) ≠ 0 := by
    rw [hcast, map_mul]
    exact mul_ne_zero hs0 (mul_ne_zero hu0 hϖc)
  have ec := hτc (Units.mk0 _ hc0) rfl
  have ec' := hτ'c (Units.mk0 _ hc0') rfl
  have hmain : toAb E Ω (τ'⁻¹ * τ) = art (localIdele E v uc) := by
    have e1 : toAb E Ω τ = (art (localIdele E v (Units.mk0 _ hc0)))⁻¹ := by
      rw [← ec, map_inv, inv_inv]
    rw [map_mul, ec', e1, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, uc]
    rw [hcast, map_mul]
    field_simp
  refine ⟨τ'⁻¹ * τ * ρ ^ (normV v - 1), mul_mem hσ0 (pow_mem hρ _), ?_, ?_⟩
  · rw [map_mul, map_pow, hmain, hρz, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hz]
    congr 1
    rw [mul_comm x, mul_inv_cancel_left]
  · have e : (τ'⁻¹ * τ * ρ ^ (normV v - 1)) π = (τ'⁻¹ * τ) π := by
      rw [AlgEquiv.mul_apply, GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem E Ω v A hA (ϖ : E) π hπ ρ hρ]
    rw [e]
    exact hval

end
end
end
