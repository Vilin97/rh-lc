module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemPowsSUnitsChooseTStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndexStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMonStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupLocalKummerNormsNeTopStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPowStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnitStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowOfSUnitLocalPowerAtPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_of_mem_sUnits_union_of_mem_finPow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]
      [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))),
      p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ →
      ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  intro p F _ _ _ _ ζ S T hp hζ hS hT y hy hyS
  by_contra hne
  have hne' : ∀ r : F, r ^ p ≠ (y : F) := fun r hr => hne ⟨r, hr⟩
  have hadm : AdmP p F (S ∪ T) :=
    (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).2 S (S ∪ T) Finset.subset_union_left hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ y (S ∪ T) hp hζ hadm hy hne' ?_
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  unfold finNorm
  refine le_iInf₂ fun v hv => ?_
  rcases Finset.mem_union.1 hv with hv | hv
  · have h1 : y ∈ powSub p (algebraMap F (v.adicCompletion F)) :=
      (iInf₂_le (f := fun w (_ : w ∈ S) => powSub p (algebraMap F (w.adicCompletion F))) v hv) hyS
    obtain ⟨r, hr⟩ := h1
    have : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F (v.adicCompletion F) _ (y : F) r hp.pos y.ne_zero hr]
    exact le_top
  · exact le_trans
      (iInf₂_le (f := fun w (_ : w ∈ T) => powSub p (algebraMap F (w.adicCompletion F))) v hv)
      ((GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1 F (v.adicCompletion F) _ (y : F))

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowOfSUnitLocalPowerAtPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.pow_of_sUnit_localPower_at_places : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  first | exact @GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow | exact GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow | (intros; apply GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupPowersEqTopAtPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_union_sup_finPow_eq_top :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  intro p F _ _ _ S T hp hS hST hA
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS.1
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  have key : ∀ v ∈ T, ∃ w ∈ sUnits F S,
      w⁻¹ * (a * x) ∈ powSub p (algebraMap F (v.adicCompletion F)) ∧
        ∀ v' ∈ T, v' ≠ v → w ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
    intro v hv
    obtain ⟨u, hu, hnu, hu'⟩ := hA v hv
    obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) (u : F))
      (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)) hp (hS.2 v (hTS v hv))
      (by rw [hval]; exact (mem_sUnits F S u).1 hu v (hTS v hv))
      (by rw [hval]; exact hy v hv) (fun r h => hnu ⟨r, h⟩)
    refine ⟨u ^ k, pow_mem hu k, ⟨r, ?_⟩, fun v' hv' hne => pow_mem (hu' v' hv' hne) k⟩
    have hu0 : algebraMap F (v.adicCompletion F) (u : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, hr, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
      map_pow, inv_mul_cancel_left₀ (pow_ne_zero k hu0)]
  choose! w hwS hw1 hw2 using key
  have huU : ∏ v ∈ T, w v ∈ sUnits F (S ∪ T) := by
    refine prod_mem fun t ht => ?_
    rw [mem_sUnits]
    intro v hv
    exact (mem_sUnits F S _).1 (hwS t ht) v fun h => hv (Finset.mem_union_left _ h)
  have hsq : (∏ v ∈ T, w v)⁻¹ * (a * x) ∈ finPow p F T := by
    simp only [finPow, Subgroup.mem_iInf]
    intro v hv
    rw [← Finset.mul_prod_erase T w hv, mul_inv, mul_right_comm]
    refine mul_mem (hw1 v hv) (inv_mem (prod_mem fun t ht => ?_))
    exact hw2 t (Finset.mem_of_mem_erase ht) v hv (Finset.ne_of_mem_erase ht).symm
  have hx : x = ((∏ v ∈ T, w v) * a⁻¹) * ((∏ v ∈ T, w v)⁻¹ * (a * x)) := by
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup (mul_mem huU (inv_mem haU)) hsq

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupPowersEqTopAtPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  first | exact @GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top | exact GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top | (intros; apply GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemKummerNormsOfLocalNorms

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem index_eq_relIndex_mul_index_sup_normThm {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

theorem inf_le_of_index_count_normThm {G : Type} [CommGroup G] (p : ℕ) (hp : 0 < p)
    (U W D N : Subgroup G) (s k t : ℕ)
    (hWD : W ≤ D) (hND : N ≤ D) (hk : k + 1 = 2 * s) (hW0 : W.index ≠ 0)
    (hW : W.index ≤ p ^ (2 * s)) (hWU : W.relIndex U = p ^ k) (hD : p ^ t ≤ D.index)
    (hN0 : N.relIndex U ≠ 0) (hN : p * N.relIndex U ≤ p ^ t) : D ⊓ U ≤ N := by
  have e1 := index_eq_relIndex_mul_index_sup_normThm U W
  have e2 := index_eq_relIndex_mul_index_sup_normThm U D
  have h4 : p ^ (2 * s) = p ^ k * p := by
    rw [← pow_succ, hk]
  have hUW0 : (U ⊔ W).index ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hW0 e1
  have hUW : (U ⊔ W).index ≤ p := by
    rw [e1, hWU, h4] at hW
    exact Nat.le_of_mul_le_mul_left hW (by positivity)
  have hUD : (U ⊔ D).index ≤ p :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hUW0)
      (Subgroup.index_dvd_of_le (sup_le_sup_left hWD U))) hUW
  have h3 : N.relIndex U ≤ D.relIndex U := by
    have : p * N.relIndex U ≤ p * D.relIndex U := by
      calc p * N.relIndex U ≤ D.relIndex U * (U ⊔ D).index := by
            rw [← e2]; exact hN.trans hD
        _ ≤ D.relIndex U * p := Nat.mul_le_mul_left _ hUD
        _ = p * D.relIndex U := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hp
  have e3 : N.relIndex (D ⊓ U) * D.relIndex U = N.relIndex U := by
    have := Subgroup.relIndex_inf_mul_relIndex N D U
    rwa [inf_eq_left.mpr hND] at this
  have hD0 : D.relIndex U ≠ 0 := by
    intro h; rw [h, mul_zero] at e3; exact hN0 e3.symm
  have hm0 : N.relIndex (D ⊓ U) ≠ 0 := by
    intro h; rw [h, zero_mul] at e3; exact hN0 e3.symm
  have hm : N.relIndex (D ⊓ U) ≤ 1 := by
    rw [← e3] at h3
    have : N.relIndex (D ⊓ U) * D.relIndex U ≤ 1 * D.relIndex U := by rwa [one_mul]
    exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hD0)
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem pows_le_finPow_normThm (p : ℕ) (F : Type) [Field F] [NumberField F] (U : Subgroup Fˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : pows p U ≤ finPow p F S := by
  rintro _ ⟨y, -, rfl⟩
  have h : ∀ {L : Type} [Field L] (φ : F →+* L), powMonoidHom p y ∈ powSub p φ := by
    intro L _ φ
    exact ⟨φ y, by simp⟩
  exact Subgroup.mem_iInf.mpr fun _ => Subgroup.mem_iInf.mpr fun _ => h _

theorem mem_pows_sUnits_normThm (p : ℕ) (hp : 0 < p) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ sUnits F S)
    (h : ∃ r : F, r ^ p = (y : F)) : y ∈ pows p (sUnits F S) := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hr, zero_pow hp.ne'])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · intro v hv
    have h1 := hy v hv
    have h2 : v.valuation F r ^ p = 1 := by
      rw [← map_pow, hr]; exact h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne').mp h2
  · ext
    simp [hr]

theorem sUnit_mem_kNorm_of_mem_finNorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns x hx hxl
  classical
  have hp0 := hp.pos
  obtain ⟨T, hST, hcard, hsq, hA⟩ := GlobalTheory.T.exists_places_with_pth_roots_and_separating_units p F ζ δ S hp hζ hS hδ hns
  have hsurj := GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places p F S T hp hS hST hA
  have hinj := GlobalTheory.T.pow_of_sUnit_localPower_at_places p F ζ S T hp hζ hS hsurj
  have hmono : sUnits F S ≤ sUnits F (S ∪ T) := fun y hy v hv =>
    hy v (fun h => hv (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inl h))
  have hS' : AdmP p F (S ∪ T) :=
    (exists_admissiblePlaces_superset_and_mono p F hp0).2 S (S ∪ T) Finset.subset_union_left hS
  obtain ⟨hN0, hN⟩ := GlobalTheory.T.first_inequality_sUnits_prime_degree p F ζ δ (S ∪ T) hp hζ hS' (hmono hδ) hns
  have ht : tNon p F δ (S ∪ T) = tNon p F δ S := by
    unfold tNon
    congr 1
    ext v
    simp only [Finset.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, h'⟩
      · obtain ⟨r, hr⟩ := hsq v h
        exact absurd hr (h' r)
    · rintro ⟨h, h'⟩
      exact ⟨Or.inl h, h'⟩
  rw [ht] at hN
  obtain ⟨-, hD⟩ := GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ δ S hp hζ
  obtain ⟨hW0, hW⟩ := GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp0
  have hU := (pTor_pIdx_sUnits p F ζ (S ∪ T) hp hζ).2
  unfold pIdx at hU
  have hinf : finPow p F S ⊓ sUnits F (S ∪ T) = pows p (sUnits F (S ∪ T)) ⊓ sUnits F (S ∪ T) := by
    apply le_antisymm
    · rintro y ⟨h1, h2⟩
      exact ⟨mem_pows_sUnits_normThm p hp0 F _ y h2 (hinj y h2 h1), h2⟩
    · exact inf_le_inf_right _ (pows_le_finPow_normThm p F _ S)
  have hWU : (finPow p F S).relIndex (sUnits F (S ∪ T)) =
      p ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, hU]
  obtain ⟨k1, k2⟩ := GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp0
  have hWD : finPow p F S ≤ finNorm p F δ S := iInf₂_mono fun _ _ => k1 _ _ _ _
  have hND : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => k2 _ _ _ _
  refine inf_le_of_index_count_normThm p hp0 (sUnits F (S ∪ T)) (finPow p F S) (finNorm p F δ S)
    _ _ _ _ hWD hND ?_ hW0 hW hWU hD hN0 hN ⟨hxl, hmono hx⟩
  rw [Finset.card_union_of_disjoint hST]
  omega

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemKummerNormsOfLocalNormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.sUnit_mem_kummerNorms_of_local_norms : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm | exact GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm | (intros; apply GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm <;> assumption)
end
end
