module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerBernoulliCoeffExpansionModDenominat
import Mathlib.Algebra.Order.Star.Rat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SingleInvMulGroupRingSumOverUnitsInv

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.single_inv_mul_groupRingSumOverUnitsInv :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (R Γ : Type) [CommRing R] [Group Γ] (φ : (ZMod M)ˣ →* Γ) (c : R)
      (f : ZMod M → R),
      MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ c * sumEl φ f = sumEl φ fun b => c * f (yCl a b) := by
  intro M a _ ha R Γ _ _ φ c f
  unfold sumEl yCl
  rw [Finset.mul_sum]
  symm
  rw [← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime a ha))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have key : ((a : ZMod M))⁻¹ * ((b : ZMod M) * (a : ZMod M)) = (b : ZMod M) := by
    rw [mul_comm (b : ZMod M), ← mul_assoc, mul_comm _ (a : ZMod M), ZMod.coe_mul_inv_eq_one a ha, one_mul]
  rw [MonoidAlgebra.single_mul_single]
  simp only [Equiv.coe_mulRight, map_mul, mul_inv_rev, Units.val_mul, ZMod.coe_unitOfCoprime, key]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bridge

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.twistedStickelbergerElements_agree :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (Γ : Type) [CommGroup Γ] (φ : (ZMod M)ˣ →* Γ) (k : ℕ),
      B4.yEl k a ha φ = Stk.yForm k a φ ∧ B4.ytEl k a φ = Stk.ytEl k a φ ∧ B4.xEl a φ = Stk.xEl a φ ∧
      B4.coefMap ℚ Γ = Stk.cf ℚ Γ := by
  intro M a _ ha Γ _ φ k
  refine ⟨?_, rfl, rfl, ?_⟩
  · have e : B4.sumEl φ (B4.Ek M k) = Stk.sumEl φ (Stk.Ev M k) := rfl
    have hneg : ∀ f : ZMod M → ℚ, (Stk.sumEl φ fun b => -f b) = -Stk.sumEl φ f := by
      intro f
      simp [Stk.sumEl, Finset.sum_neg_distrib]
    have hE : Stk.Eva M k a =
        fun b => Stk.Ev M k b + -((a : ℚ) ^ k * Stk.Ev M k (Stk.yCl a b)) := by
      funext b
      simp [Stk.Eva, sub_eq_add_neg]
    simp only [B4.yEl, B4.thetaEl]
    rw [e, sub_mul, one_mul, mul_neg, Stk.single_inv_mul_groupRingSumOverUnitsInv, Stk.yForm, hE, Stk.sumEl_add, hneg]
    abel
  · apply MonoidAlgebra.ringHom_ext
    · intro n
      simp [B4.coefMap_single]
    · intro g
      simp [B4.coefMap_single]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.GroupRingIntAtDivSmulOfPadicValNatLe

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.groupRing_intAt_div_smul_of_padicValNat_le :
    ∀ (l : ℕ) [Fact l.Prime] (M D t : ℕ), 0 < M → 0 < D → t + padicValNat l D ≤ padicValNat l M →
      ∀ (Γ : Type) [CommGroup Γ] (z : MonoidAlgebra ℤ Γ), B4.IntAt l t (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z) := by
  intro l _ M D t hM hD ht Γ _ z g
  have hp : l.Prime := Fact.out
  have hcoef : (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z).coeff g = ((M : ℚ) / (D : ℚ)) * (z.coeff g : ℚ) := by
    simp [Stk.cf]
  rw [hcoef]
  have hdvdM : l ^ (padicValNat l D + t) ∣ M :=
    (pow_dvd_pow l (by omega)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hdvdD : l ^ padicValNat l D ∣ D := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  obtain ⟨k, hk⟩ := hdvdM
  obtain ⟨E, hE⟩ := hdvdD
  have hnd : ¬ l ∣ E := by
    intro hl
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    conv_rhs => rw [hE]
    rw [pow_succ]
    simpa only [Nat.padicValNat_def] using Nat.mul_dvd_mul_left (l ^ padicValNat l D) hl
  have hE0 : E ≠ 0 := by
    rintro rfl
    simp at hE
    omega
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hEq : (E : ℚ) ≠ 0 := by exact_mod_cast hE0
  have hMq : (M : ℚ) = (l : ℚ) ^ (padicValNat l D + t) * k := by exact_mod_cast hk
  have hDq : (D : ℚ) = (l : ℚ) ^ padicValNat l D * E := by exact_mod_cast hE
  have heq : (M : ℚ) / (D : ℚ) * (z.coeff g : ℚ) / (l : ℚ) ^ t = ((k : ℚ) / (E : ℚ)) * (z.coeff g : ℚ) := by
    rw [hMq, hDq, pow_add]
    field_simp
  rw [heq]
  refine (B4.Zl l).mul_mem ?_ (intCast_mem _ _)
  rw [B4.mem_Zl]
  intro hden
  apply hnd
  have h1 : (((k : ℤ) : ℚ) / ((E : ℤ) : ℚ)).den ∣ E := by
    rw [← Rat.divInt_eq_div]
    exact_mod_cast Rat.den_dvd (k : ℤ) (E : ℤ)
  push_cast at h1
  exact hden.trans h1
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerCarrySpecAndWeightOneCoeffOfOdd

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.stickelbergerCarry_spec_and_weightOne_coeff_of_odd :
    ∀ (M a : ℕ) [NeZero M], a.Coprime M → ∀ b : ZMod M,
      (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b ∧ (Odd a → Eva M 1 a b = (Eone M a b : ℚ)) := by
  intro M a _ hcop b
  have hM : (M : ℤ) ∣ (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, yCl, ← mul_assoc,
      ZMod.coe_mul_inv_eq_one a hcop, one_mul, sub_self]
  have h1 : (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b := by
    rw [jv, Int.mul_ediv_cancel' hM]
    ring
  refine ⟨h1, fun hodd => ?_⟩
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h1q : (a : ℚ) * ((yCl a b).val : ℚ) = (b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ) := by
    exact_mod_cast h1
  obtain ⟨t, ht⟩ := hodd
  have hE : (Eone M a b : ℚ) = (t : ℚ) - (jv M a b : ℚ) := by
    rw [Eone]
    have : (((a : ℤ) - 1) / 2) = t := by omega
    rw [this]
    push_cast
    rfl
  rw [hE, Eva, Ev, Ev, bcoef, bcoef, Polynomial.bernoulli_one]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_one, sub_self,
    zpow_zero, one_mul, div_one, pow_one]
  have ha : (a : ℚ) ≠ 0 := by
    rw [ht]
    push_cast
    positivity
  have hy : ((yCl a b).val : ℚ) = ((b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ)) / (a : ℚ) := by
    field_simp
    linarith [h1q]
  rw [hy]
  have hta : (a : ℚ) = 2 * t + 1 := by exact_mod_cast ht
  field_simp
  rw [hta]
  ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.TwistedBernoulliValueCongrPowMulFirst

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.twistedBernoulliValue_congr_pow_mul_first :
    ∀ (M a e : ℕ) [NeZero M], a.Coprime M → Odd a → ∀ b : ZMod M, ∃ z : ℤ,
      Eva M (e + 1) a b = (((b.val : ℤ) ^ e * Eone M a b : ℤ) : ℚ) + (M : ℚ) / (dk (e + 1) : ℚ) * z := by
  intro M a e _ ha ho b
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  have h1 := (stickelbergerCarry_spec_and_weightOne_coeff_of_odd M a ha b).1
  obtain ⟨z1, hz1⟩ := stickelbergerBernoulliCoeff_expansion_mod_denominator M e b.val hM0
  obtain ⟨z2, hz2⟩ := stickelbergerBernoulliCoeff_expansion_mod_denominator M e (yCl a b).val hM0
  obtain ⟨⟨z3, hz3⟩, ⟨w, hw⟩⟩ := exists_binomial_expansion_mod_sq (b.val : ℤ) (jv M a b) M e
  rw [← h1, mul_pow] at hz3 hw
  obtain ⟨c, hc⟩ := ho
  have h2 : ((a : ℤ) - 1) / 2 = c := by omega
  have h4 : (a : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  have h6 : (c : ℚ) = ((a : ℚ) - 1) / 2 := by rw [h4]; ring
  have q3 : (a : ℚ) ^ (e + 1) * ((yCl a b).val : ℚ) ^ (e + 1) =
      (b.val : ℚ) ^ (e + 1) + ((e : ℚ) + 1) * (b.val : ℚ) ^ e * ((M : ℚ) * (jv M a b : ℚ)) + (M : ℚ) ^ 2 * z3 := by
    exact_mod_cast hz3
  have qw : (a : ℚ) ^ e * ((yCl a b).val : ℚ) ^ e = (b.val : ℚ) ^ e + (M : ℚ) * w := by
    exact_mod_cast hw
  have hdk : (dk (e + 1) : ℚ) = 2 * ((e : ℚ) + 1) * (primorial (e + 1 + 1) : ℚ) := by
    rw [dk]; push_cast; ring
  refine ⟨2 * z1 - 2 * (a : ℤ) ^ (e + 1) * z2 - 2 * (primorial (e + 1 + 1) : ℤ) * z3
    + ((e : ℤ) + 1) * (primorial (e + 1 + 1) : ℤ) * a * w, ?_⟩
  rw [Eva, Ev, Ev, hz1, hz2, Eone, h2, hdk]
  push_cast
  rw [h6]
  have e1 : ∀ R : ℚ, (a : ℚ) ^ (e + 1) * (((yCl a b).val : ℚ) ^ (e + 1) / (((e : ℚ) + 1) * M) -
      ((yCl a b).val : ℚ) ^ e / 2 + R) =
      ((a : ℚ) ^ (e + 1) * ((yCl a b).val : ℚ) ^ (e + 1)) / (((e : ℚ) + 1) * M) -
        a * ((a : ℚ) ^ e * ((yCl a b).val : ℚ) ^ e) / 2 + (a : ℚ) ^ (e + 1) * R := by
    intro R; ring
  rw [e1, q3, qw]
  field_simp
  ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.YNear

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.yNear :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a r : ℕ) (ha : a.Coprime N), Odd a → l ^ (r + ck l (e + 1) + 1) ∣ N → IntAt l r (yEl (e + 1) a ha φ - coefMap ℚ Γ (ytEl e a φ)) := by
  intro l _ Γ _ _ N _ φ e a r ha hodd hdvd
  have hy := (Stk.twistedStickelbergerElements_agree N a ha Γ φ (e + 1)).1
  have hyt := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.1
  have hcf := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.2.2
  choose z hz using Stk.twistedBernoulliValue_congr_pow_mul_first N a e ha hodd
  rw [hy, hyt, hcf]
  have key : Stk.yForm (e + 1) a φ - Stk.cf ℚ Γ (Stk.ytEl e a φ)
      = ((N : ℚ) / (Stk.dk (e + 1) : ℚ)) • Stk.cf ℚ Γ (Stk.sumEl φ (fun b => -z b)) := by
    rw [Stk.cf_sumEl]
    unfold Stk.yForm Stk.ytEl
    rw [map_neg, Stk.cf_sumEl]
    unfold Stk.sumEl
    rw [neg_sub_neg, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hz _, MonoidAlgebra.smul_single]
    first
      | rw [← MonoidAlgebra.single_sub]
      | erw [← Finsupp.single_sub]
    congr 1
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hN0 : N ≠ 0 := NeZero.ne N
  have hv := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN0).mp hdvd
  apply Stk.groupRing_intAt_div_smul_of_padicValNat_le l N (Stk.dk (e + 1)) r (Nat.pos_of_ne_zero hN0) (Stk.dk_pos (Nat.succ_pos e))
  have hck : ck l (e + 1) = padicValNat l (Stk.dk (e + 1)) := rfl
  omega
end
end
