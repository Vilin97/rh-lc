module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastIsUnitPadicInt

section

@[expose] public section

namespace GlobalTheory.PadicInversePower

open Formalism.ConjugateSelfDual

theorem natCast_isUnit_padicInt (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem inv_pow_mem (l : ℕ) [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (((x : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (x : ZMod (l ^ 0)).val = 0 := by
      haveI : NeZero (l ^ 0) := ⟨by simp⟩
      exact Nat.lt_one_iff.mp (by simpa only [pow_zero] using ZMod.val_lt (x : ZMod (l ^ 0)))
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [pow_zero, inv_one]; exact c.O.one_mem
    · simp only [Nat.cast_zero, zero_pow he.ne', inv_zero]; exact c.O.zero_mem
  · let n := (x : ZMod (l ^ r)).val
    have hcop : l.Coprime n :=
      (ZMod.val_coe_unit_coprime x).symm.of_dvd_left (dvd_pow_self l hr.ne')
    have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop
    obtain ⟨u, hu⟩ := (natCast_isUnit_padicInt l n hnd).pow e
    have key : ((n : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ↑u⁻¹ := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [key]
    exact c.O.algebraMap_mem _

end GlobalTheory.PadicInversePower
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherTail

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have hi : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have hm : minpoly ℚ_[l] x = (minpoly ℤ_[l] x).map (algebraMap ℤ_[l] ℚ_[l]) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hm,
    spectralValue_le_one_iff ((minpoly.monic hi).map _)]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobOfShapiroSystem

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZGlobAsm

theorem norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem c hx

theorem inv_pow_val_mem (l : ℕ) [Fact l.Prime] (c : Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ ∈ c.O :=
  _root_.GlobalTheory.PadicInversePower.inv_pow_mem l c e r x

theorem eta_compat (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l)
    (hχ : ∀ r x, χ r x ∈ c.O)
    (hχc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => ((((x : ZMod (l ^ (r + 1))).val : ℕ) : Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x)
        ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
  _root_.GlobalTheory.PadicNormCastBounds.twist_compat l c e χ hχ hχc r x

end GlobalTheory.KZGlobAsm

namespace GlobalTheory.KZ

end GlobalTheory.KZ
end
end
