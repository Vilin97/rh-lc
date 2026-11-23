module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnitStatement
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlacePowAndNotPowStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIndependentPrimeRelIndexSubgroups

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_eq_prime_of_generated {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (E K : Subgroup G) (x : G) (hxE : x ∈ E) (hxK : x ∉ K) (hxp : x ^ p ∈ K)
    (hgen : ∀ y ∈ E, ∃ k : ℕ, y / x ^ k ∈ K) : K.relIndex E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c : E ⧸ K.subgroupOf E := QuotientGroup.mk (⟨x, hxE⟩ : E) with hc
  have ho : orderOf c = p := by
    apply orderOf_eq_prime
    · rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hxp
    · rw [hc, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxK
  have hall : ∀ y : E ⧸ K.subgroupOf E, y ∈ Submonoid.powers c := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen y y.2
    refine ⟨k, ?_⟩
    simp only [hc]
    rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa using hk
  rw [Subgroup.relIndex, Subgroup.index, ← ho]
  exact (orderOf_eq_card_of_forall_mem_powers hall).symm

theorem exists_independent_prime_relIndex_subgroups (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι]
    (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ) (hp : p.Prime)
    (hH : H.relIndex U = p ^ m) (h1 : ∀ i, good i → U ⊓ H ≤ K i)
    (h2 : ∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i)
    (h2' : ∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i)
    (h3 : ∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) (k : ℕ) (hk : k ≤ m) :
    ∃ T : Finset ι, T.card = k ∧ (∀ i ∈ T, good i) ∧
      (∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j) ∧
      ∃ D : Subgroup G, (∀ x, x ∈ D ↔ ∀ i ∈ T, x ∈ K i) ∧ D.relIndex U = p ^ k := by
  induction k with
  | zero =>
    refine ⟨∅, rfl, by simp, by simp, ⊤, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, hg, hA, D, hD, hDi⟩ := ih (by omega)
    have hx : ∃ x ∈ U, x ∈ D ∧ x ∉ H := by
      by_contra hcon
      push Not at hcon
      have heq : D ⊓ U = H ⊓ U := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨hcon x b a, b⟩
        · rintro ⟨a, b⟩
          exact ⟨(hD x).2 fun i hi => h1 i (hg i hi) ⟨b, a⟩, b⟩
      have h4 : D.relIndex U = H.relIndex U := by
        rw [← Subgroup.inf_relIndex_right D U, heq, Subgroup.inf_relIndex_right]
      rw [hDi, hH] at h4
      have := Nat.pow_right_injective hp.two_le h4
      omega
    obtain ⟨x, hxU, hxD, hxH⟩ := hx
    obtain ⟨j, hj, hxj⟩ := h3 x hxU hxH
    have hjT : j ∉ T := fun h => hxj ((hD x).1 hxD j h)
    refine ⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hT], ?_, ?_, K j ⊓ D, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hj
      · exact hg i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨x, hxU, hxj, fun l hl hli => ?_⟩
        rcases Finset.mem_insert.1 hl with rfl | hl
        · exact absurd rfl hli
        · exact (hD x).1 hxD l hl
      · obtain ⟨u, huU, hui, hu⟩ := hA i hi
        obtain ⟨n, hn⟩ := h2' j hj x hxU hxj u huU
        refine ⟨u / x ^ n, U.div_mem huU (U.pow_mem hxU n), ?_, fun l hl hli => ?_⟩
        · intro h
          apply hui
          have := (K i).mul_mem h ((K i).pow_mem ((hD x).1 hxD i hi) n)
          simpa using this
        · rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hn
          · exact (K l).div_mem (hu l hl hli) ((K l).pow_mem ((hD x).1 hxD l hl) n)
    · intro y
      simp only [Subgroup.mem_inf, hD, Finset.forall_mem_insert]
    · have h5 : (K j).relIndex (D ⊓ U) = p :=
        relIndex_eq_prime_of_generated hp (D ⊓ U) (K j) x ⟨hxD, hxU⟩ hxj (h2 j hj x hxU)
          (fun y hy => h2' j hj x hxU hxj y hy.2)
      rw [← Subgroup.relIndex_inf_mul_relIndex, h5, hDi, pow_succ, mul_comm]

theorem exists_indep_prime_index : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι] (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ), p.Prime → H.relIndex U = p ^ m → (∀ i, good i → U ⊓ H ≤ K i) → (∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i) → (∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i) → (∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) → ∃ T : Finset ι, T.card = m ∧ (∀ i ∈ T, good i) ∧ ∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j := by
  intro p G ι _ _ U H K good m hp hH h1 h2 h2' h3
  obtain ⟨T, a, b, c, -⟩ :=
    exists_independent_prime_relIndex_subgroups p G ι U H K good m hp hH h1 h2 h2' h3 m le_rfl
  exact ⟨T, a, b, c⟩

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemPowsSUnitsChooseT

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_sup_zpowers_chooseT (p : ℕ) {G : Type} [CommGroup G] (Q : Subgroup G) (d : G)
    (hp : p.Prime) (hd : d ^ p ∈ Q) (hn : d ∉ Q) :
    Q.relIndex (Q ⊔ Subgroup.zpowers d) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.relIndex_sup_left]
  have h := Subgroup.relIndex_ker (Subgroup.zpowers d) (QuotientGroup.mk' Q)
  rw [QuotientGroup.ker_mk', MonoidHom.map_zpowers, Nat.card_zpowers] at h
  rw [h]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hd
  · exact fun e => hn ((QuotientGroup.eq_one_iff _).1 e)

theorem mem_pows_sUnits_chooseT (p : ℕ) (hp : p ≠ 0) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) (hx : x ∈ sUnits F S) (r : F)
    (hr : r ^ p = (x : F)) : x ∈ pows p (sUnits F S) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hr, zero_pow hp])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_sUnits]
    intro v hv
    have h := (mem_sUnits F S x).1 hx v hv
    rw [← hr, map_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le hp).1 h
  · ext
    simp [hr]

theorem exists_auxiliary_places_prime : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns
  classical
  have hQU : pows p (sUnits F S) ≤ sUnits F S := by
    rintro _ ⟨y, hy, rfl⟩
    exact (sUnits F S).pow_mem hy p
  have hdd : δ ^ p ∈ pows p (sUnits F S) := ⟨δ, hδ, rfl⟩
  have hdn : δ ∉ pows p (sUnits F S) := by
    rintro ⟨y, -, hy⟩
    exact hns (y : F) (by rw [← hy]; simp)
  have hHU : pows p (sUnits F S) ⊔ Subgroup.zpowers δ ≤ sUnits F S :=
    sup_le hQU ((Subgroup.zpowers_le).2 hδ)
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = S.card + Fintype.card (InfinitePlace F) :=
    ⟨S.card + Fintype.card (InfinitePlace F) - 1, by omega⟩
  have hidx : (pows p (sUnits F S) ⊔ Subgroup.zpowers δ).relIndex (sUnits F S) = p ^ m := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hHU
    have h2 : (pows p (sUnits F S)).relIndex (sUnits F S) = _ :=
      (pTor_pIdx_sUnits p F ζ S hp hζ).2
    rw [relIndex_sup_zpowers_chooseT p _ _ hp hdd hdn, h2, ← hm, pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F),
      Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := fun v x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hpw : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ),
      x ^ p ∈ powSub p (algebraMap F (v.adicCompletion F)) := fun v x =>
    ⟨algebraMap F (v.adicCompletion F) x, by rw [Units.val_pow_eq_pow_val, map_pow]⟩
  obtain ⟨T, hT, hgood, hA⟩ := exists_indep_prime_index p Fˣ (HeightOneSpectrum (𝓞 F)) (sUnits F S)
    (pows p (sUnits F S) ⊔ Subgroup.zpowers δ)
    (fun v => powSub p (algebraMap F (v.adicCompletion F)))
    (fun v => v ∉ S ∧ ∃ r : v.adicCompletion F,
      r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) m hp hidx
    (by
      rintro v ⟨-, hv⟩
      refine le_trans inf_le_right (sup_le ?_ ((Subgroup.zpowers_le).2 hv))
      rintro _ ⟨y, -, rfl⟩
      exact hpw v y)
    (fun v _ x _ => hpw v x)
    (by
      rintro v ⟨hv, -⟩ x hx hx' y hy
      obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) x)
        (algebraMap F (v.adicCompletion F) y) hp (hS.2 v hv)
        (by rw [hval]; exact (mem_sUnits F S x).1 hx v hv)
        (by rw [hval]; exact (mem_sUnits F S y).1 hy v hv)
        (fun r hr => hx' ⟨r, hr⟩)
      refine ⟨k, r, ?_⟩
      have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by simp
      rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, map_div₀, map_pow, hr]
      field_simp)
    (by
      intro x hx hxH
      obtain ⟨v, h1, h2, h3⟩ := GlobalTheory.T.exists_place_pow_and_not_pow' p F ζ δ x S hp hζ δ.ne_zero x.ne_zero hns
        (fun k r h => hxH (by
          have h4 : x / δ ^ k ∈ pows p (sUnits F S) := by
            refine mem_pows_sUnits_chooseT p hp.ne_zero F S _
              ((sUnits F S).div_mem hx ((sUnits F S).pow_mem hδ k)) r ?_
            have hδ0 := δ.ne_zero
            rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, h]
            field_simp
          have h5 := Subgroup.mul_mem_sup h4 (Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) k)
          rwa [div_mul_cancel] at h5))
      exact ⟨v, ⟨h1, h2⟩, fun ⟨r, hr⟩ => h3 r hr⟩)
  refine ⟨T, ?_, by rw [hT, hm], fun v hv => (hgood v hv).2, hA⟩
  rw [Finset.disjoint_right]
  exact fun v hv => (hgood v hv).1

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemPowsSUnitsChooseTStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_places_with_pth_roots_and_separating_units : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  first | exact @GlobalTheory.CNorm.exists_auxiliary_places_prime | exact GlobalTheory.CNorm.exists_auxiliary_places_prime | (intros; apply GlobalTheory.CNorm.exists_auxiliary_places_prime <;> assumption)
end
end
