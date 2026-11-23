module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelWithOddPrimeFirstNumber

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_prime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧
      ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  intro E _ _ _ H l
  have hM1 : l.M ≠ 1 := by have := l.three_le; omega
  obtain ⟨n, hn, hnM⟩ := Nat.exists_prime_and_dvd hM1
  have hodd : Odd n := Odd.of_dvd_nat l.odd hnM
  have h3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  refine ⟨n, hn, hodd, fun A₀ hA₀ => ?_⟩
  have hmap : (l.Mb ⊔ Ideal.span {(n : 𝓞 E)}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ⊔ Ideal.span {(n : 𝓞 E)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  have hMn : Ideal.span {(l.M : 𝓞 E)} ≤ Ideal.span {(n : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hnM)
  refine ⟨⟨n, h3, hodd, l.Mb ⊔ Ideal.span {(n : 𝓞 E)}, ?_, ?_, ?_, A₀, hA₀⟩,
    ⟨l.M, l.three_le, l.odd, l.Mb, l.fromK, l.prod, l.coprime, Nat.lcm l.A A₀, Nat.lcm_pos l.A_pos hA₀⟩,
    rfl, rfl, ⟨hnM, le_sup_left, Nat.dvd_lcm_right _ _⟩, ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩⟩
  · apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        intro a ha
        exact ⟨Ideal.mem_sup_left ha.1, ha.2⟩
      · refine Ideal.span_mono ?_
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ _⟩
    · exact Ideal.span_le.2 fun a ha => ha.1
  · rw [hmap, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
    set N : Ideal (𝓞 E) := Ideal.span {(n : 𝓞 E)}
    apply le_antisymm
    · refine sup_le (sup_le hMn ?_) (sup_le ?_ ?_) <;>
        first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
    · calc N = N * (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by rw [l.coprime, Ideal.mul_top]
        _ = l.Mb * N ⊔ N * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.mul_sup, mul_comm N l.Mb]
        _ ≤ _ := sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_right)
  · rw [hmap, eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left le_sup_left

end GlobalTheory.ZM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelWithOddPrimeFirstNumberStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_level_with_odd_prime_first_number : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧ ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  first | exact @GlobalTheory.ZM.exists_prime_level | exact GlobalTheory.ZM.exists_prime_level | (intros; apply GlobalTheory.ZM.exists_prime_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_moduli_prime_power_fullLevel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ j : ℕ, ∀ l : Level H, l.M = n → l.A = (n ^ j) ^ 2 → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.ZM.exists_moduli_prime_power_level | exact GlobalTheory.ZM.exists_moduli_prime_power_level | (intros; apply GlobalTheory.ZM.exists_moduli_prime_power_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvdStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.nonempty_moduli_of_level_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  first | exact @GlobalTheory.nonempty_moduli_of_dvd | exact GlobalTheory.nonempty_moduli_of_dvd | (intros; apply GlobalTheory.nonempty_moduli_of_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeNonemptyAtEveryLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem moduli_nonempty_all_levels : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  intro h1 h2 h3 h4 E _ _ _ H D l hD
  obtain ⟨n, hn, hodd, hl⟩ := GlobalTheory.T.exists_level_with_odd_prime_first_number E H l
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_moduli_prime_power_fullLevel h1 h2 h3 h4 E H D n hD hn hodd
  obtain ⟨l₀, l₂, hM, hA, h02, h2'⟩ := hl ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)
  exact GlobalTheory.T.nonempty_cmModuli_of_deeper_level h1 h2 h3 E H D l l₂ hD h2'
    (GlobalTheory.T.nonempty_moduli_of_level_dvd h1 h2 E H D l₀ l₂ hD h02 (hj l₀ hM hA))

end GlobalTheory.ZM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeNonemptyAtEveryLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.moduliScheme_nonempty_at_every_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  first | exact @GlobalTheory.ZM.moduli_nonempty_all_levels | exact GlobalTheory.ZM.moduli_nonempty_all_levels | (intros; apply GlobalTheory.ZM.moduli_nonempty_all_levels <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Moduli

theorem moduli_scheme_exists : N1ab :=
  GlobalTheory.T.moduliScheme_nonempty_at_every_level GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.theorem_of_cube_polAbelianScheme GlobalTheory.T.theta_uniformisation_complex_abelian_varieties

end GlobalTheory.Moduli
end
end
