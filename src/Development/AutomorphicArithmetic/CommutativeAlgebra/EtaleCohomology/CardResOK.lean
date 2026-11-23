module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrysCopy
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
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
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FlatOfDvr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.BcCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.IntMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ThetaSetupAlgebraMaps

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal IsLocalRing Polynomial Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AinfK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem l_res : ((l : ℕ) : ResidueField ↥(OL K)) = 0 := by
  rw [← map_natCast (residue ↥(OL K))]
  exact (residue_eq_zero_iff _).mpr (l_mem_max K)

theorem exists_card : ∃ a : ℕ, a ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ a := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  exact ⟨n, n.ne_zero, by rw [Nat.card_eq_fintype_card, hn]⟩

variable {K} {a : ℕ} [NeZero a]


omit [NeZero a] in
theorem res_pow (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ResidueField ↥(OL K)) : x ^ l ^ a = x := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  rw [← h, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_teich (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ↥(OL K)) :
    ∃ w : ↥(OL K), w ^ l ^ a = w ∧ residue _ w = residue _ x := by
  obtain ⟨_, hc, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete K
  have h1 := one_lt_pow_l l a
  have hm : (X ^ l ^ a - X : (↥(OL K))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨w, hw, hx⟩ := HenselianRing.is_henselian (I := maximalIdeal ↥(OL K)) _ hm x (by
      rw [← residue_eq_zero_iff]; simp [res_pow h]) (by
      change IsUnit (residue _ _)
      have : ((l : ResidueField ↥(OL K))) ^ a = 0 := by rw [l_res, zero_pow (NeZero.ne a)]
      simp [derivative_X_pow, this])
  refine ⟨w, by simpa [sub_eq_zero] using hw, ?_⟩
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hx

theorem exists_toOm (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : Om l) (hx : x ^ l ^ a = x) :
    ∃ w : ↥(OL K), toOm K w = x := by
  classical
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have h1 := one_lt_pow_l l a
  choose r hr using residue_surjective (R := ↥(OL K))
  choose s hs hs' using fun y => exists_teich h (r y)
  have hinj : Function.Injective fun y => toOm K (s y) := fun y z e => by
    rw [← hr y, ← hr z, ← hs', ← hs', toOm_injective K e]
  have hm : (X ^ l ^ a - X : (Om l)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hmem : ∀ y : Om l, y ∈ (X ^ l ^ a - X : (Om l)[X]).roots.toFinset ↔ y ^ l ^ a = y := fun y => by
    simp [mem_roots hm.ne_zero, sub_eq_zero]
  have hsub : Finset.univ.image (fun y => toOm K (s y)) = (X ^ l ^ a - X : (Om l)[X]).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
      rw [hmem, ← map_pow, hs]
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, h]
      refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
      rw [Polynomial.natDegree_X_pow_sub_X h1]
  obtain ⟨z, -, hz⟩ := Finset.mem_image.1 (hsub ▸ (hmem x).2 hx)
  exact ⟨_, hz⟩

theorem hasUnr (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : HasUnr a K :=
  ⟨IntermediateField.adjoin_le_iff.2 fun x hx => by
    obtain ⟨w, rfl⟩ := exists_toOm h x hx
    exact (w : ↥K.1).2⟩

theorem pow_eq_of_root (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) {x : Om l} (hx : x ∈ K.1) {m : ℕ}
    (h0 : 0 < m) (hm : ¬ l ∣ m) (h1 : x ^ m = 1) : x ^ l ^ a = x := by
  have h2 : (⟨x, hx⟩ : ↥K.1) ∈ OL K := IsIntegral.of_pow h0 (by
    rw [show (⟨x, hx⟩ : ↥K.1) ^ m = 1 from Subtype.ext h1]; exact isIntegral_one)
  set y : ↥(OL K) := ⟨_, h2⟩
  have hy : y ^ m = 1 := Subtype.ext (Subtype.ext h1)
  obtain ⟨k, hk⟩ : ∃ k, l ^ a = k + 1 := ⟨l ^ a - 1, by have := one_lt_pow_l l a; omega⟩
  have hr0 : residue _ y ≠ 0 := ((IsUnit.of_pow_eq_one hy h0.ne').map _).ne_zero
  have hr : residue _ (y ^ k) = 1 := by
    have := res_pow h (residue _ y)
    rw [hk, pow_succ] at this
    rw [map_pow]
    exact mul_right_cancel₀ hr0 (by rw [this, one_mul])
  have hg := mul_geom_sum (y ^ k) m
  rw [← pow_mul, mul_comm k, pow_mul, hy, one_pow, sub_self] at hg
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  have hs : ∑ i ∈ Finset.range m, (y ^ k) ^ i ≠ 0 := fun e => hm (by
    have := congrArg (residue _) e

    simp only [map_sum, map_pow (residue _) (y ^ k), hr, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, map_zero] at this
    exact (CharP.cast_eq_zero_iff _ l m).1 this)
  have h3 : y ^ k = 1 := sub_eq_zero.1 ((mul_eq_zero.1 hg).resolve_right hs)
  have h4 : x ^ k = 1 := congrArg (toOm K) h3
  rw [hk, pow_succ, h4, one_mul]

theorem Kunr_eq (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : Kunr l a = K0 K := by
  refine le_antisymm (le_inf (hasUnr h).le (Kunr_le_Kur l a)) ?_
  have key : ∀ c ∈ K0 K, ‖c‖ ≤ 1 → c ∈ Kunr l a := fun c hc h1 => by
    obtain ⟨n, z, ω, hω, rfl⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c hc h1
    refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    obtain ⟨h2, m, h0, hm, h3⟩ := hω i
    exact IntermediateField.subset_adjoin _ _ (pow_eq_of_root h h2.1 h0 hm h3)
  intro c hc
  rcases le_total ‖c‖ 1 with h1 | h1
  · exact key c hc h1
  · exact inv_mem_iff.1 (key _ (inv_mem hc) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1))


variable (l a) in
theorem free_Wq : Module.Free ℤ_[l] (Wq l a) := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : FaithfulSMul ℤ_[l] (Wq l a) := (faithfulSMul_iff_algebraMap_injective _ _).2 fun u v h => by
    have := congrArg (GlobalTheory.TameFrob.iotaO l a) h
    simp only [GlobalTheory.TameFrob.iotaO_algebraMap] at this
    exact Subtype.val_injective ((algebraMap ℚ_[l] (Om l)).injective this)
  infer_instance


variable (l a) in
theorem finrank_Wq : Module.finrank ℤ_[l] (Wq l a) = a := by
  have := free_Wq l a
  have h := (splitEquiv (AlgHom.id ℤ_[l] (Wq l a))).toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h
  simpa using h


attribute [local instance] GlobalTheory.TameFrob.algK GlobalTheory.TameFrob.isFractionRing in
variable (l a) in
theorem finrank_Kunr : Module.finrank ℚ_[l] ↥(Kunr l a) = a := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : IsScalarTower ℤ_[l] (Wq l a) ↥(Kunr l a) := IsScalarTower.of_algebraMap_eq fun u =>
    Subtype.ext (GlobalTheory.TameFrob.iotaO_algebraMap l a u).symm
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing ℤ_[l] ℚ_[l] (Wq l a) ↥(Kunr l a), finrank_Wq]

variable (K)

def fK : ℕ := Module.finrank ℚ_[l] ↥(K0 K)

theorem card_res' : fK K ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ fK K := by
  obtain ⟨a, ha, h⟩ := exists_card K
  have : NeZero a := ⟨ha⟩
  have e : fK K = a := by rw [fK, ← Kunr_eq h, finrank_Kunr]
  rw [e]
  exact ⟨ha, h⟩

instance : NeZero (fK K) := ⟨(card_res' K).1⟩

theorem card_res : Nat.card (ResidueField ↥(OL K)) = l ^ fK K := (card_res' K).2

theorem Kunr_fK : Kunr l (fK K) = K0 K := Kunr_eq (card_res K)

end GlobalTheory.AinfK
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FKEqResDeg

section

@[expose] public section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.WeilDeligne GlobalTheory.Pst
open GlobalTheory.BKReal IsLocalRing Formalism.BasicNotions.Examples₂.LB

namespace GlobalTheory.AinfK

theorem fK_eq_resDeg {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w)
    (hj : Induces Bw) : fK Bw.Kw = resDeg l w := by
  have hN := normV_eq_pow (hj.mem_placesOver h)
  refine Nat.pow_right_injective hl.out.two_le (le_antisymm ?_ ?_)
  · obtain ⟨-, ω, hω, -⟩ := exists_gen l (fK Bw.Kw)
    have h1 := one_lt_pow_l l (fK Bw.Kw)
    have hm : ω ∈ K0 Bw.Kw := Kunr_fK Bw.Kw ▸ IntermediateField.subset_adjoin _ _ (show ω ^ l ^ fK Bw.Kw = ω by
      rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
    have h2 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_of_deg (by simp)) ⟨ω, hm.2⟩
    rw [mul_one, mul_zero, pow_zero, frobUr_pow_root _ _ (l ^ fK Bw.Kw - 1) (by omega)
      (fun hd => hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd))
      (Subtype.ext hω.pow_eq_one)] at h2
    have h3 : ω = ω ^ l ^ resDeg l w :=
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (weilToGK Bw h (frob h)).2 _ hm.1).symm.trans h2
    have h4 := one_lt_normV w
    rw [hN] at h4
    have h5 : ω ^ (l ^ resDeg l w - 1) = 1 := mul_right_cancel₀ (hω.ne_zero (by omega)) (by
      rw [← pow_succ, Nat.sub_add_cancel h4.le, one_mul, ← h3])
    have := Nat.le_of_dvd (by omega) (hω.dvd_of_pow_eq_one _ h5)
    change l ^ _ ≤ l ^ _
    omega
  · change l ^ _ ≤ l ^ _
    rw [← hN, ← card_res]
    let u : 𝓞 E →+* ↥Bw.Kw.1 :=
      (Bw.j.comp ((algebraMap E Ω).comp (algebraMap (𝓞 E) E))).codRestrict Bw.Kw.1 fun x => Bw.j_E _
    let v : 𝓞 E →+* ↥(OL Bw.Kw) := u.codRestrict (OL Bw.Kw) fun x =>
      (map_isIntegral_int u (RingOfIntegers.isIntegral x)).tower_top
    have hk : ∀ x, ((residue _).comp v) x = 0 ↔ x ∈ w.asIdeal := fun x => by
      rw [RingHom.comp_apply, residue_eq_zero_iff, mem_max, ← h x, hj.valuation_lt_one_iff]
      rfl
    have := OL_resFinite Bw.Kw
    exact Nat.card_le_card_of_injective (Ideal.Quotient.lift w.asIdeal _ fun x hx => (hk x).2 hx)
      (RingHom.lift_injective_of_ker_le_ideal _ _ fun x hx => (hk x).1 hx)

end GlobalTheory.AinfK
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.OkDvr

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

theorem ok_dvr_pf [FiniteDimensional ℚ_[l] K] : IsDomain (OK l K) ∧ IsDiscreteValuationRing (OK l K) ∧
    ∀ a : OK l K, a ≠ 0 → ∃ k : ℕ, a ∣ (l : OK l K) ^ k := by
  have := OK_dvr (l := l) (K := K)
  refine ⟨inferInstance, OK_dvr, ?_⟩
  intro a ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hlm : ((l : ℕ) : OK l K) ∈ IsLocalRing.maximalIdeal (OK l K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]
    have e : (((((l : ℕ) : OK l K) : K)) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one.ne
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hlm
  refine ⟨n, ?_⟩
  have h1 : a ∣ ϖ ^ n := ⟨(↑u⁻¹ : OK l K), by rw [hu, mul_comm (u : OK l K), mul_assoc, Units.mul_inv, mul_one]⟩
  exact h1.trans (pow_dvd_pow_of_dvd hlm n)

end CrystallineSemistableComparison.Pb.Kap
end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CardResOK

section

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.Pst TensorProduct Module Matrix CrystallineSemistableComparison
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam

private theorem mem_OK_iff {l : ℕ} [Fact l.Prime] (K : FinExt l) (x : ↥K.1) : x ∈ OK l K.1 ↔ x ∈ OL K := by
  rw [OK_eq]; rfl

private def okEquiv {l : ℕ} [Fact l.Prime] (K : FinExt l) : ↥(OL K) ≃+* ↥(OK l K.1) where
  toFun b := ⟨b.1, (mem_OK_iff K b.1).2 b.2⟩
  invFun c := ⟨c.1, (mem_OK_iff K c.1).1 c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem card_res_OK {l : ℕ} [Fact l.Prime] (K : FinExt l) [IsLocalRing ↥(OK l K.1)] :
    Nat.card (IsLocalRing.ResidueField ↥(OK l K.1)) = l ^ GlobalTheory.AinfK.fK K := by
  rw [← GlobalTheory.AinfK.card_res K]
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (okEquiv K)).toEquiv).symm

private theorem dvd_pow_sub {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {q : ℕ} (hq : q ≠ 0)
    (hc : Nat.card (IsLocalRing.ResidueField R) = q) {t : R} (ht : Irreducible t) (x : R) : t ∣ x ^ q - x := by
  have : Finite (IsLocalRing.ResidueField R) := Nat.finite_of_card_ne_zero (by rwa [hc])
  letI := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have h := FiniteField.pow_card (IsLocalRing.residue R x)
  rw [← Nat.card_eq_fintype_card, hc] at h
  rw [← Ideal.mem_span_singleton, ← ht.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h, sub_self]

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.congBC :
    UpperTheory.Ru.crystallineComparison.CongBC := by
  intro E Ω _ _ _ _ _ l _ L _ H θ w hl n ϑ hC A hA O _ _ _ Bw hB
  obtain ⟨C, p, f, hp, hpw, hN, hO, ϖ, T, γ, m, hϖ, hid, hT⟩ := hC
  have epl : p = l := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp Fact.out).2 hne)
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have h := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at h
      rw [← h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hl)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  subst epl
  have hNv : normV w = p ^ f := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hf : resDeg p w = f := by
    rw [resDeg, hNv, Nat.log_pow hp.one_lt]
  subst hf
  have hpos : 0 < resDeg p w := Nat.pos_of_ne_zero fun h0 =>
    w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 (by rw [hN, h0, pow_zero]))
  haveI := Bw.Kw.2
  obtain ⟨hD, hV, -⟩ := CrystallineSemistableComparison.Pb.Kap.ok_dvr_pf (l := p) (K := Bw.Kw.1)
  haveI := hD
  haveI := hV
  haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing
  obtain ⟨φ, hφ, hφi⟩ := UpperTheory.Gal.Seam.intMap E Ω p w A hA O Bw hB
  have hcard : Nat.card (IsLocalRing.ResidueField ↥(OK p Bw.Kw.1)) = p ^ resDeg p w := by
    rw [card_res_OK, GlobalTheory.AinfK.fK_eq_resDeg Bw hA hB]
  obtain ⟨C', u, hu, -, hOnto, -, hLies⟩ :=
    UpperTheory.Gal.Seam.bcCover E ↥Bw.Kw.1 (Ow w) ↥(OK p Bw.Kw.1) L (UpperTheory.Gal.Seam.kOf Bw) φ hφ H θ C
  have hirr := hφi ϖ hϖ
  obtain ⟨T', κ, hκ, hid'⟩ := UpperTheory.Ru.crystallineComparison.ptIdBC p (p ^ resDeg p w) n (Ow w) ↥(OK p Bw.Kw.1) φ ϖ hϖ hirr
    (dvd_pow_sub (pow_ne_zero _ hp.ne_zero) hcard hirr) C.Y C'.Y C.p C'.p u hu T (fun j => (hT j).1) hid
  refine ⟨hD, hV, hpos, hNv, hcard, C', hOnto hO, φ ϖ, T', γ, m, hirr, hid', fun j => ⟨(hκ j).2.2, ?_, (hT j).2.2⟩⟩
  exact hLies (γ j) (T j).Z (T j).p (T j).r (m j) (hT j).1 (hT j).2.1 (T' j).Z (κ j) (T' j).p (T' j).r (hκ j).1
    (hκ j).2.1.symm (hκ j).2.2
end
end
end
