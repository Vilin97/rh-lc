module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneFixQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnitsGen
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.CycDescend

section

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cycDescend :
    ∀ (a b : ℕ) [NeZero (a * b)] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {a * b} ℚ C] (ζ : C) (F : IntermediateField ℚ C), a.Coprime b → IsPrimitiveRoot ζ (a * b) → (∀ p : ℕ, p.Prime → p ∣ b → UnramAt F p) → F ≤ ℚ⟮ζ ^ b⟯ := by
  intro a b _ C _ _ _ ζ F hab hζ hunr
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (NeZero.ne (a * b))
  haveI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {a * b} ℚ C
  set χ := IsCyclotomicExtension.Rat.galEquivZMod (a * b) C with hχ
  have hcomm : ∀ σ τ : Gal(C/ℚ), τ * σ * τ⁻¹ = σ := by
    intro σ τ
    apply χ.injective
    rw [map_mul, map_mul, map_inv, mul_comm (χ τ), mul_assoc, mul_inv_cancel, mul_one]
  haveI : F.fixingSubgroup.Normal := ⟨fun σ hσ τ => by rw [hcomm]; exact hσ⟩
  have hFF : fixedField F.fixingSubgroup = F := IsGalois.fixedField_fixingSubgroup F
  haveI hgF : IsGalois ℚ F := by
    have h := IsGalois.of_fixedField_normal_subgroup F.fixingSubgroup
    rw [hFF] at h
    convert h
  have hin : ∀ p : ℕ, p.Prime → p ∣ b → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal →
      w.asIdeal.inertia Gal(C/ℚ) ≤ F.fixingSubgroup := by
    intro p hp hpb w hw σ hσ
    have hk := (UpperTheory.V.CF.ineFixQ F C p hp).mp (hunr p hp hpb) w hw hσ
    rw [MonoidHom.mem_ker] at hk
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hc := UpperTheory.V.CF.resTo_commutes ℚ F C σ ⟨x, hx⟩
    rw [hk, AlgEquiv.one_apply] at hc
    exact hc.symm
  have hsup : ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p ≤
      F.fixingSubgroup.map χ.toMonoidHom := by
    refine iSup₂_le fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
    obtain ⟨P, hPm, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 C) (Ideal.span {(p : ℤ)})
    haveI := hPm
    haveI := hPl
    have hpP : (p : 𝓞 C) ∈ P := by
      have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
      rw [Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.under_def,
        Ideal.mem_comap] at h1
      simpa using h1
    let w : HeightOneSpectrum (𝓞 C) := ⟨P, hPm.isPrime, fun h => by
      rw [h, Ideal.mem_bot] at hpP
      exact (Nat.cast_ne_zero.mpr hpp.ne_zero) hpP⟩
    rw [← KStar.Ram.map_inertia_eq p P]
    exact Subgroup.map_mono (hin p hpp hpb w hpP)
  rw [← IsGalois.fixedField_fixingSubgroup ℚ⟮ζ ^ b⟯, IntermediateField.le_iff_le]
  intro σ hσ
  have hfix : σ (ζ ^ b) = ζ ^ b := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
    (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hker : χ σ ∈ (ZMod.unitsMap (Dvd.intro b rfl : a ∣ a * b)).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one]
    rw [map_pow, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (a * b) C σ hζ.pow_eq_one,
      ← pow_mul] at hfix
    have hmod : (χ σ).val.val * b ≡ 1 * b [MOD a * b] := by
      rw [one_mul]
      have h2 := (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod.mp hfix
      rw [← hζ.eq_orderOf] at h2
      exact h2
    have hk := Nat.ModEq.mul_right_cancel' hb0 hmod
    rw [← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk
  have hmem := hsup (UpperTheory.V.CF.unitsGen a b hab hker)
  rw [Subgroup.mem_map] at hmem
  obtain ⟨τ, hτ, hτσ⟩ := hmem
  have hτσ' : τ = σ := χ.injective hτσ
  rwa [hτσ'] at hτ
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwRamSplit

section

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem kwRam_split (M N : ℕ) (hN : 0 < N) :
    ∃ a b n : ℕ, N = a * b ∧ a ∣ M ^ n ∧ b.Coprime M := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hc : N.Coprime M
    · exact ⟨1, N, 0, by simp, by simp, hc⟩
    · obtain ⟨p, hp, hpN, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      obtain ⟨N', rfl⟩ := hpN
      have hN' : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
      have hlt : N' < p * N' := by have := hp.two_le; nlinarith
      obtain ⟨a, b, n, rfl, ha, hb⟩ := ih N' hlt hN'
      refine ⟨p * a, b, n + 1, by ring, ?_, hb⟩
      rw [pow_succ']
      exact mul_dvd_mul hpM ha

theorem UpperTheory.V.CF.kwRam :
    ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (M : ℕ), 0 < M → (∀ p : ℕ, p.Prime → ¬ p ∣ M → UnramAt L p) → ∃ n : ℕ, Nonempty (L →ₐ[ℚ] CyclotomicField (M ^ n) ℚ) := by
  intro L _ _ _ M hM hram
  obtain ⟨N, hN, ⟨f⟩⟩ := kwHom L
  obtain ⟨a, b, n, rfl, ha, hb⟩ := kwRam_split M N hN
  have ha0 : a ≠ 0 := by rintro rfl; simp at hN
  have hb0 : b ≠ 0 := by rintro rfl; simp at hN
  have hab : a.Coprime b := Nat.Coprime.coprime_dvd_left ha (hb.pow_right n).symm
  haveI : NeZero (a * b) := ⟨hN.ne'⟩
  haveI : NeZero ((a * b : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {a * b} ℚ (CyclotomicField (a * b) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (a * b) ℚ
    · rfl
  obtain ⟨ζ, hζ⟩ : ∃ z : CyclotomicField (a * b) ℚ, IsPrimitiveRoot z (a * b) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  let F : IntermediateField ℚ (CyclotomicField (a * b) ℚ) := f.fieldRange
  let e : L ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField f
  have hF : ∀ p : ℕ, p.Prime → p ∣ b → UnramAt F p := by
    intro p hp hpb
    have hpM : ¬ p ∣ M := fun h => hp.not_dvd_one (Nat.Coprime.gcd_eq_one hb ▸ Nat.dvd_gcd hpb h)
    letI : Algebra F L := e.symm.toRingHom.toAlgebra
    exact unramIff.2.2 F L p hp (hram p hp hpM)
  have hle := cycDescend a b (CyclotomicField (a * b) ℚ) ζ F hab hζ hF
  have hζb : IsPrimitiveRoot (ζ ^ b) a := by
    have h := hζ.pow_of_dvd hb0 (dvd_mul_left b a)
    rwa [Nat.mul_div_cancel a (Nat.pos_of_ne_zero hb0)] at h
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have hint : IsIntegral ℚ (ζ ^ b) := (hζb.isIntegral hapos).tower_top
  haveI : NeZero (M ^ n) := ⟨pow_ne_zero _ hM.ne'⟩
  haveI : NeZero ((M ^ n : ℕ) : ℚ) := ⟨by exact_mod_cast pow_ne_zero _ hM.ne'⟩
  haveI : IsCyclotomicExtension {M ^ n} ℚ (CyclotomicField (M ^ n) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (M ^ n) ℚ
    · rfl
  obtain ⟨ω, hω⟩ : ∃ z : CyclotomicField (M ^ n) ℚ, IsPrimitiveRoot z (M ^ n) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  have hq0 : M ^ n / a ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (pow_pos hM n) ha) hapos).ne'
  have hη := hω.pow_of_dvd hq0 (Nat.div_dvd_of_dvd ha)
  rw [Nat.div_div_self ha (pow_ne_zero _ hM.ne')] at hη
  have hmem : ω ^ (M ^ n / a) ∈ (minpoly ℚ (ζ ^ b)).aroots (CyclotomicField (M ^ n) ℚ) := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζb hapos, Polynomial.mem_aroots]
    refine ⟨Polynomial.cyclotomic_ne_zero _ _, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hη.isRoot_cyclotomic hapos
  let g := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨_, hmem⟩
  exact ⟨n, ⟨(g.comp (IntermediateField.inclusion hle)).comp e.toAlgHom⟩⟩
end
end
