module

public import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

-- Source module: Development.AutomorphicArithmetic.QuadraticCharacters.LogDerivAtOne

section

@[expose] public section

open ArithmeticFunction

namespace HostParam

structure AbField where
  N : ℕ
  N_pos : 0 < N
  H : Subgroup (ZMod N)ˣ

namespace AbField

variable (E : AbField)

abbrev Gal : Type := (ZMod E.N)ˣ ⧸ E.H

def res : (ZMod E.N)ˣ →* E.Gal := QuotientGroup.mk' E.H

def IsReal : Prop := (-1 : (ZMod E.N)ˣ) ∈ E.H

def inertiaUnits (p : ℕ) : Subgroup (ZMod E.N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd E.N p)).ker

def inertia (p : ℕ) : Subgroup E.Gal := (E.inertiaUnits p).map E.res

def Ramified (p : ℕ) : Prop := E.inertia p ≠ ⊥

def IsModulus (M : ℕ) : Prop := ∃ h : M ∣ E.N, (ZMod.unitsMap h).ker ≤ E.H

noncomputable def conductor : ℕ := sInf {M : ℕ | E.IsModulus M}

def chars : Set (DirichletCharacter ℂ E.N) := {χ | ∀ u ∈ E.H, χ (u : ZMod E.N) = 1}

noncomputable def toGalChar (χ : DirichletCharacter ℂ E.N) (hχ : χ ∈ E.chars) : E.Gal →* ℂˣ :=
  QuotientGroup.lift E.H χ.toUnitHom (fun u hu => by
    rw [MonoidHom.mem_ker]; ext; simpa using hχ u hu)

end AbField

def SplitsIn (d p : ℕ) : Prop :=
  p ≠ d ∧ (p = 2 → d % 8 = 7) ∧ (p ≠ 2 → jacobiSym (-(d : ℤ)) p = 1)

noncomputable def quadCharNeg (d : ℕ) : DirichletCharacter ℂ d :=
  if h : d.Prime then
    letI : Fact d.Prime := ⟨h⟩
    (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  else 1

noncomputable def AbField.chOf (E : AbField) (d : ℕ) (h : d ∣ E.N) : DirichletCharacter ℂ E.N :=
  DirichletCharacter.changeLevel h (quadCharNeg d)

end HostParam
end
end

-- Source module: Development.AutomorphicArithmetic.QuadraticCharacters.GaussRoot

section

@[expose] public section

open NumberField IntermediateField

namespace HostParam

namespace SlopeTestRemainingChoices.GaussRoot

theorem exists_gauss {K : Type} [Field K] [CharZero K] {d : ℕ} [hd : Fact d.Prime]
    (hd4 : d % 4 = 3) {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ∃ G : K, G ^ 2 = -(d : K) ∧ ∀ (σ : K →+* K) (a : ℕ), a.Coprime d → σ ζ = ζ ^ a →
      σ G = ((quadraticChar (ZMod d) (a : ZMod d) : ℤ) : K) * G := by
  haveI : NeZero d := ⟨hd.out.ne_zero⟩
  have hζ1 : ζ ^ d = 1 := hζ.pow_eq_one
  let χ : MulChar (ZMod d) K := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom K)
  let ψ : AddChar (ZMod d) K := AddChar.zmodChar d hζ1
  have hchar : ringChar (ZMod d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hchar)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod d)).comp _
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  refine ⟨gaussSum χ ψ, ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχq hψ, ZMod.card]
    have hm : χ (-1) = -1 := by
      simp only [χ, MulChar.ringHomComp_apply, quadraticChar_neg_one hchar, ZMod.card,
        ZMod.χ₄_nat_three_mod_four hd4]
      simp
    rw [hm]
    ring
  · intro σ a ha hσ
    have hσψ : ∀ x : ZMod d, σ (ψ x) = ψ (a * x) := by
      intro x
      calc σ (ψ x) = σ (ζ ^ x.val) := rfl
        _ = ζ ^ (a * x.val) := by rw [map_pow, hσ, ← pow_mul]
        _ = ψ ((a * x.val : ℕ) : ZMod d) := (AddChar.zmodChar_apply' hζ1 _).symm
        _ = ψ (a * x) := by
          push_cast
          rw [ZMod.natCast_zmod_val]
    let u : (ZMod d)ˣ := ZMod.unitOfCoprime a ha
    have hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift u) := by

      simp only [gaussSum, map_sum, map_mul, AddChar.mulShift_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hσψ]
      simp [χ, u]
    rw [hG, gaussSum_mulShift_eq, hχq.inv]
    simp [χ, u]

theorem eq_or_neg {K : Type} [Field K] {a b c : K} (ha : a ^ 2 = c) (hb : b ^ 2 = c) :
    a = b ∨ a = -b := sq_eq_sq_iff_eq_or_eq_neg.mp (ha.trans hb.symm)

theorem ne_zero {K : Type} [Field K] [CharZero K] {d : ℕ} (hd : d.Prime) {b : K}
    (hb : b ^ 2 = -(d : K)) : b ≠ 0 := by
  rintro rfl
  have : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne_zero
  apply this
  rw [← neg_eq_zero, ← hb]
  simp

end SlopeTestRemainingChoices.GaussRoot

namespace AbField
variable (E : AbField)

end AbField

end HostParam
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.IsCMFieldOfIsChiField

section

@[expose] public section

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.isCMField_of_isChiField :
    ∀ (ψ : PChar) (e q d : ℕ), q.Prime → q % 4 = 3 → ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E → IsCMField E := by
  intro ψ e q d hq hq4 E _ _ hE
  obtain ⟨N, hN, j, ζ, -, -, hqN, -, hζ, hτ⟩ := hE
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.out⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.of_algHom j
  have hζq : IsPrimitiveRoot (ζ ^ (N / q)) q :=
    hζ.pow (NeZero.pos N) (Nat.div_mul_cancel hqN).symm
  obtain ⟨G, hG2, hGσ⟩ := HostParam.SlopeTestRemainingChoices.GaussRoot.exists_gauss hq4 hζq
  have hGL : G ∈ j.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
    intro τ hτL
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτL
    have hfix : ∀ x : E, τ (j x) = j x := fun x => hτL _ (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    obtain ⟨-, -, hjq, -⟩ := (hτ τ a ha.symm).1 hfix
    have hprim : IsPrimitiveRoot (ζ ^ a) N := by
      rw [ha]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime q :=
      Nat.Coprime.coprime_dvd_right hqN ((hζ.pow_iff_coprime (NeZero.pos N) a).1 hprim)
    have hquad : quadraticChar (ZMod q) (a : ZMod q) = 1 := by
      have h := jacobiSym.legendreSym.to_jacobiSym q (a : ℤ)
      rw [hjq] at h
      unfold legendreSym at h
      rw [Int.cast_natCast] at h
      exact h
    have h := hGσ (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ) a hcop (by
      rw [RingHom.coe_coe, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm])
    rw [hquad] at h
    simpa using h
  obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 hGL
  have hx2 : x ^ 2 = -(q : E) := by
    apply j.injective
    change j (x ^ 2) = j (-(q : E))
    rw [map_pow, hx, hG2, map_neg, map_natCast]
  haveI : IsTotallyComplex E := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
      ComplexEmbedding.isReal_iff]
    intro hr
    have hc := RingHom.congr_fun hr x
    rw [ComplexEmbedding.conjugate_coe_eq] at hc
    have him : (w.embedding x).im = 0 := Complex.conj_eq_iff_im.1 hc
    have hz2 : (w.embedding x) ^ 2 = -(q : ℂ) := by
      rw [← map_pow, hx2, map_neg, map_natCast]
    have hre := congrArg Complex.re hz2
    simp [sq, him] at hre
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq.pos
    nlinarith [mul_self_nonneg (w.embedding x).re]⟩
  exact NumberField.IsCMField.of_isAbelianGalois E
end
end
