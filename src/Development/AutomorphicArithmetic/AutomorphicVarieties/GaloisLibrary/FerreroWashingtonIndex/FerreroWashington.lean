module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardClDualOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardRangeInfTorsionLeIndexPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ConjEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbedDeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.POddRelIndexLe
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ReflOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HMinus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.UnitSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.UnrJPrime
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToKOf
import Mathlib.NumberTheory.NumberField.ClassNumber

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PTwo

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.pTwo :
    ∀ (C : Type) [CommGroup C] [Finite C] (J : C →* C), (∀ x, J (J x) = x) →
      (powR (C := C) 2).index ≤
        ((difR J).relIndex (minK J) * Nat.card (difR J ⊓ torK (C := C) 2 : Subgroup C)) ^ 2 := by
  intro C _ _ J hJ
  classical
  have hcard : ∀ {G H : Type} [Group G] [Group H] (f : G →* H),
      Nat.card G = Nat.card f.ker * Nat.card f.range := by
    intro G H _ _ f
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  set T := torK (C := C) 2 with hT
  set D := difR J with hD
  set K := minK J with hK
  have memT : ∀ x : C, x ∈ T ↔ x ^ 2 = 1 := fun x => by simp [hT, torK]
  have memK : ∀ x : C, x ∈ K ↔ J x * x = 1 := fun x => by simp [hK, minK]
  have memD : ∀ x : C, x ∈ D ↔ ∃ y, y / J y = x := fun x => by simp [hD, difR]
  have hDK : D ≤ K := by
    intro x hx
    obtain ⟨y, rfl⟩ := (memD x).1 hx
    rw [memK, map_div, hJ, div_mul_div_comm, mul_comm (J y) y, div_self']
  have h1 : (powR (C := C) 2).index = Nat.card T := by
    have e1 := hcard (powMonoidHom 2 : C →* C)
    have e2 := (powR (C := C) 2).card_mul_index
    have hpos : 0 < Nat.card (powR (C := C) 2) := Nat.card_pos
    have e3 : Nat.card (powR (C := C) 2) * (powR (C := C) 2).index =
        Nat.card (powR (C := C) 2) * Nat.card T := by
      rw [e2, mul_comm]
      exact e1
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  let g : T →* C := (MonoidHom.id C / J).comp T.subtype
  have e4 := hcard g
  have r1 : Nat.card g.range ≤ Nat.card (D ⊓ T : Subgroup C) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨t, rfl⟩
    have gt : g t = t.1 / J t.1 := rfl
    rw [gt, Subgroup.mem_inf]
    refine ⟨(memD _).2 ⟨t.1, rfl⟩, ?_⟩
    rw [memT, div_pow, ← map_pow, (memT _).1 t.2, map_one, div_one]
  have r2 : Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := by
    have hm : ∀ x : g.ker, (x.1.1 : C) ∈ K ⊓ T := by
      intro x
      have hx : g x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hT' : x.1.1 ^ 2 = 1 := (memT _).1 x.1.2
      have hd : x.1.1 / J x.1.1 = 1 := hx
      have hJx : J x.1.1 = x.1.1 := (div_eq_one.1 hd).symm
      refine Subgroup.mem_inf.2 ⟨(memK _).2 ?_, x.1.2⟩
      rw [hJx, ← pow_two, hT']
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (K ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  let incl : (K ⊓ T : Subgroup C) →* K := Subgroup.inclusion inf_le_left
  let h : (K ⊓ T : Subgroup C) →* K ⧸ D.subgroupOf K := (QuotientGroup.mk' (D.subgroupOf K)).comp incl
  have e5 := hcard h
  have r3 : Nat.card h.range ≤ D.relIndex K :=
    le_of_le_of_eq (Subgroup.card_le_card_group _) rfl
  have r4 : Nat.card h.ker ≤ Nat.card (D ⊓ T : Subgroup C) := by
    have hm : ∀ x : h.ker, (x.1.1 : C) ∈ D ⊓ T := by
      intro x
      have hx : h x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hx2 : incl x.1 ∈ D.subgroupOf K := (QuotientGroup.eq_one_iff _).1 hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hx2, (Subgroup.mem_inf.1 x.1.2).2⟩
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (D ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  rw [h1]
  set r := D.relIndex K
  set d := Nat.card (D ⊓ T : Subgroup C)
  have s1 : Nat.card T ≤ (r * d) * d := by
    rw [e4]
    apply Nat.mul_le_mul _ r1
    calc Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := r2
      _ = Nat.card h.ker * Nat.card h.range := e5
      _ ≤ d * r := Nat.mul_le_mul r4 r3
      _ = r * d := mul_comm _ _
  have s2 : (r * d) * d ≤ (r * d) ^ 2 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simp [hr]
    · rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left d hr)
  exact s1.trans s2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnCyc

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.sgnCyc :
    ∀ (f n c N : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L] (γ : (ZMod (f * 2 ^ n))ˣ), Odd f → 1 < f → 2 ≤ n → c.Coprime (f * 2 ^ n) → Odd c → (MonoidAlgebra.of ℤ _ γ - 1) ^ N ∈ Ideal.span {thetaH (f * 2 ^ n) c, 1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod (f * 2 ^ n))ˣ), ((2 : ℕ) : MonoidAlgebra ℤ (ZMod (f * 2 ^ n))ˣ)} → (difR (clMap (cE L))).relIndex (minK (clMap (cE L))) ≤ (2 ^ (Subgroup.zpowers γ).index) ^ N := by
  intro f n c N _ L _ _ _ _ γ hf hf1 hn hc ho hmem
  have hM : 2 < f * 2 ^ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith
  obtain ⟨φ, hφ⟩ := sgnUnit (f * 2 ^ n) c L hc ho hM
  obtain ⟨h1, h2, h3, h4⟩ := sgnStab (f * 2 ^ n) L φ
  refine (hMinus L _ (embT (f * 2 ^ n) L φ) (evenF (-1 : (ZMod (f * 2 ^ n))ˣ))
    (unrJ f n L hf hf1 hn) (unitSurj f n L hf hf1 hn) h1 h2).trans ?_
  haveI : Fact (2 < f * 2 ^ n) := ⟨hM⟩
  refine sgnAlg _ (-1) γ (thetaH (f * 2 ^ n) c) N _ (by simp) ?_ h3 ?_ hmem
  · intro h
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    exact ZMod.neg_one_ne_one h'
  · have h5 := (sgnE (embT (f * 2 ^ n) L φ)).sub_mem (h3 _ hφ (ZMod.unitOfCoprime c hc)⁻¹)
      ((sgnE (embT (f * 2 ^ n) L φ)).nsmul_mem h4 ((c - 1) / 2))
    convert h5 using 1
    funext s
    rw [(thetaFull (f * 2 ^ n) c hc ho hM).2 s]
    have hi : (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod (f * 2 ^ n))ˣ) : ZMod (f * 2 ^ n)) = (c : ZMod (f * 2 ^ n))⁻¹ := by
      rw [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime]
    rw [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, mul_one]
    simp only [gc, Units.val_mul, hi, Int.cast_sub, Int.cast_natCast]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.StickH

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.stickH :
    ∀ (M c : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L], c.Coprime M → Odd c → 2 < M → (cycRep M L).asAlgebraHom (thetaH M c * (1 - MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ))) = 0 := by
  intro M c _ L _ _ _ hc hodd hM

  rw [(thetaFull M c hc hodd hM).1, map_sum]
  refine LinearMap.ext fun x => ?_
  simp only [Representation.asAlgebraHom_single, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply]
  have key : ∀ y : Cl L, ∑ s : (ZMod M)ˣ, gc M c ↑s • (cycRep M L s) (Additive.ofMul y) = 0 := by
    intro y
    simp only [cycRep_apply, ← ofMul_zpow, ← ofMul_prod, clA, ofMul_eq_zero]
    haveI : Fact (1 < M) := ⟨by omega⟩
    set u : (ZMod M)ˣ := ZMod.unitOfCoprime c hc with hu_def
    set k : ℤ := (((c - 1) / 2 : ℕ) : ℤ) with hk
    refine (Stick.coef M L y).2
      (fun s => (c : ℤ) * (if s = u⁻¹ then 1 else 0) - (k + 1) * (if s = 1 then 1 else 0)
        - k * (if s = -1 then 1 else 0)) (fun t => gc M c ↑t) ?_
    intro t
    haveI : NeZero (t : ZMod M) := ⟨t.ne_zero⟩
    have hlt := ZMod.val_lt (t : ZMod M)
    have hneg : ((-(t : ZMod M)).val : ℤ) = M - (t : ZMod M).val := by
      rw [ZMod.val_neg_of_ne_zero (t : ZMod M), Nat.cast_sub hlt.le]
    have hu : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) = (c : ZMod M)⁻¹ := by
      rw [← ZMod.inv_coe_unit]
      rfl
    have hmod : c * ((c : ZMod M)⁻¹ * t).val % M = (t : ZMod M).val := by
      rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← mul_assoc,
        ZMod.coe_mul_inv_eq_one c hc, one_mul]
    have hdiv := Nat.div_add_mod (c * ((c : ZMod M)⁻¹ * t).val) M
    rw [hmod] at hdiv
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Units.val_one, Units.val_neg,
      neg_one_mul, hu, hneg, gc]
    generalize c * ((c : ZMod M)⁻¹ * t).val / M = q at hdiv ⊢
    have hz : (M : ℤ) * q + ((t : ZMod M).val : ℤ) = c * (((c : ZMod M)⁻¹ * t).val : ℤ) := by
      exact_mod_cast hdiv
    linear_combination hz
  exact key (Additive.toMul x)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.cyc (l : ℕ) [hl : Fact l.Prime] (f : ℕ) (hf : f.Coprime l) (h1 : 1 < f) :
    ∃ B n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L],
      IsTotallyComplex L ∧ (powR (Cl L) l).index ≤ B := by
  classical
  have hf0 : 0 < f := by omega
  have hl0 : 0 < l := hl.out.pos
  have hfl0 : 0 < f * l := Nat.mul_pos hf0 hl0
  have hcodd : Odd (2 * (f * l) + 1) := ⟨f * l, by ring⟩
  have hc1 : 1 < 2 * (f * l) + 1 := by omega
  have hcfl : (2 * (f * l) + 1).Coprime (f * l) := by
    simp [Nat.coprime_mul_left_add_left]
  obtain ⟨N, n₀, hn₀2, hmem⟩ := memZ l f (2 * (f * l) + 1) hf hcodd hc1 hcfl
  obtain ⟨B, hB⟩ := ambCyc l f hf
  by_cases hl2 : l = 2
  · subst hl2
    refine ⟨((2 ^ (f * 2 ^ ee 2).totient) ^ N * B ^ N) ^ 2, n₀, ?_⟩
    intro n hn L _ _ _
    haveI : NeZero (f * 2 ^ n) := ⟨(Nat.mul_pos hf0 (pow_pos hl0 n)).ne'⟩
    have hM2 : 2 < f * 2 ^ n := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    haveI : IsCMField L := IsCyclotomicExtension.Rat.isCMField L ⟨f * 2 ^ n, Set.mem_singleton _, hM2⟩
    refine ⟨inferInstance, ?_⟩
    obtain ⟨γ, hγ1, hγidx, hγmem⟩ := hmem n hn
    have hcM : (2 * (f * 2) + 1).Coprime (f * 2 ^ n) := by
      obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hcfl
      exact Nat.coprime_mul_iff_right.mpr ⟨h1, h2.pow_right n⟩
    have hcore := core 2 (ZMod (f * 2 ^ n))ˣ (Cl L) (cycRep (f * 2 ^ n) L) (-1) γ
      (clA (f * 2 ^ n) L (-1)) (clA (f * 2 ^ n) L γ) (thetaH (f * 2 ^ n) (2 * (f * 2) + 1)) N
      (by simp) (fun x => cycRep_apply _ _ _ x) (fun x => cycRep_apply _ _ _ x)
      (stickH _ _ L hcM hcodd hM2) hγmem
    have hamb := hB n L γ (by omega) hγ1
    have hbound : Nat.card ↥(difR (clA (f * 2 ^ n) L (-1)) ⊓ torK (Cl L) 2) ≤ B ^ N :=
      hcore.trans (Nat.pow_le_pow_left hamb N)
    have hfodd : Odd f := Nat.coprime_two_right.mp hf
    obtain ⟨_, hcE2⟩ := conjEq (f * 2 ^ n) L
    have hsgn := sgnCyc f n (2 * (f * 2) + 1) N L γ hfodd h1 (by omega) hcM hcodd hγmem
    rw [← hcE2, hγidx] at hsgn
    have hinv : ∀ x : Cl L, clA (f * 2 ^ n) L (-1) (clA (f * 2 ^ n) L (-1) x) = x := by
      intro x
      apply Additive.ofMul.injective
      rw [← cycRep_apply, ← cycRep_apply, ← Module.End.mul_apply, ← map_mul]
      simp
    have hp := pTwo (Cl L) (clA (f * 2 ^ n) L (-1)) hinv
    exact hp.trans (Nat.pow_le_pow_left (Nat.mul_le_mul hsgn hbound) 2)
  · refine ⟨l * (B ^ N) ^ 2, n₀, ?_⟩
    intro n hn L _ _ _
    haveI : NeZero (f * l ^ n) := ⟨(Nat.mul_pos hf0 (pow_pos hl0 n)).ne'⟩
    have hl3 : 3 ≤ l := by
      have := hl.out.two_le
      omega
    have hM2 : 2 < f * l ^ n := by
      have : 3 ≤ l ^ n := by
        calc 3 ≤ l := hl3
          _ = l ^ 1 := (pow_one l).symm
          _ ≤ l ^ n := Nat.pow_le_pow_right hl0 (by omega)
      nlinarith
    haveI : IsCMField L := IsCyclotomicExtension.Rat.isCMField L ⟨f * l ^ n, Set.mem_singleton _, hM2⟩
    refine ⟨inferInstance, ?_⟩
    obtain ⟨γ, hγ1, _, hγmem⟩ := hmem n hn
    have hcM : (2 * (f * l) + 1).Coprime (f * l ^ n) := by
      obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hcfl
      exact Nat.coprime_mul_iff_right.mpr ⟨h1, h2.pow_right n⟩
    have hcore := core l (ZMod (f * l ^ n))ˣ (Cl L) (cycRep (f * l ^ n) L) (-1) γ
      (clA (f * l ^ n) L (-1)) (clA (f * l ^ n) L γ) (thetaH (f * l ^ n) (2 * (f * l) + 1)) N
      (by simp) (fun x => cycRep_apply _ _ _ x) (fun x => cycRep_apply _ _ _ x)
      (stickH _ _ L hcM hcodd hM2) hγmem
    have hamb := hB n L γ (by omega) hγ1
    have hbound : Nat.card ↥(difR (clA (f * l ^ n) L (-1)) ⊓ torK (Cl L) l) ≤ B ^ N :=
      hcore.trans (Nat.pow_le_pow_left hamb N)
    have hlodd : Odd l := hl.out.odd_of_ne_two hl2
    obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L (Set.mem_singleton (f * l ^ n))
      (NeZero.ne _)
    have hsplit : f * l ^ n = f * l ^ (n - 1) * l := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    have hζl : IsPrimitiveRoot (ζ ^ (f * l ^ (n - 1))) l := hζ.pow (NeZero.pos _) hsplit
    obtain ⟨_, hcE2⟩ := conjEq (f * l ^ n) L
    have hrefl := reflOdd L l _ hl2 hζl
    rw [← hcE2] at hrefl
    have hp := pOdd l (Cl L) (clA (f * l ^ n) L (-1)) hlodd hrefl
    exact hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbound 2))

theorem UpperTheory.V.FW.ferreroWashington : UpperTheory.V.Published.FerreroWashington := by
  unfold UpperTheory.V.Published.FerreroWashington
  intro l _ K _ _ _ _
  obtain ⟨f, D, hf, h1, hemb⟩ := embed l K
  obtain ⟨B, n₀, hB⟩ := cyc l f hf h1
  refine ⟨D * l ^ n₀ * B, ?_⟩
  intro n K' _ _ _ _
  obtain ⟨m, L, iF, iN, iA, iC, hm, hdeg⟩ := hemb n n₀ K'
  obtain ⟨htc, hidx⟩ := hB m hm L
  have hd := desc l K' L htc
  have hl2 : 1 < l := (Fact.out : l.Prime).one_lt
  have key : Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l).range) ≤ D * l ^ n₀ * B := by
    have e : Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l).range) = (powR (Cl K') l).index := rfl
    rw [e]
    exact hd.trans (Nat.mul_le_mul hdeg hidx)
  exact key.trans (Nat.lt_pow_self hl2).le
end
end
