module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Tactic.ToDual
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
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Lattice.Nat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSpan
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

theorem etPoint_min {X : Type} [AddCommGroup X] (Q : X → ℤ) (hQ : ∀ a, 0 ≤ Q a) (y : X) (R' : ℕ) :
    ∃ z : X, ∀ z' : X, Q (y + R' • z) ≤ Q (y + R' • z') := by
  let S : Set ℕ := Set.range fun z : X => (Q (y + R' • z)).toNat
  have hS : S.Nonempty := ⟨_, 0, rfl⟩
  obtain ⟨z, hz⟩ := Nat.sInf_mem hS
  refine ⟨z, fun z' => ?_⟩
  have h1 : sInf S ≤ (Q (y + R' • z')).toNat := Nat.sInf_le ⟨z', rfl⟩
  have h2 := hQ (y + R' • z)
  have h3 := hQ (y + R' • z')
  have h4 : (Q (y + R' • z)).toNat = sInf S := hz
  omega

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def ETSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (R' : ℕ), 2 ≤ R' → ∀ (r : ℕ) (y z : Fin r → Y),
    (∀ a : Y, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : Y, a = u + R' • t) →
    ∀ a : Y, ∃ n : ℕ, 0 < n ∧
      n • a ∈ Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETSpan

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField

theorem etSpan_holds : ETSpanStatement := by
  intro E _ _ Y _ _ _ R' hR' r y z hgen a
  set X : Submodule (𝓞 E) Y := Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b) with hX

  have hdec : ∀ a : Y, ∃ x ∈ X, ∃ t : Y, a = x + R' • t := by
    intro a
    obtain ⟨u, hu, t, rfl⟩ := hgen a
    have hspan : Submodule.span (𝓞 E) (Set.range y) ≤
        X ⊔ LinearMap.range (R' • LinearMap.id : Y →ₗ[𝓞 E] Y) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_sup]
      refine ⟨y b + R' • z b, Submodule.subset_span ⟨b, rfl⟩, R' • (-z b), ⟨-z b, rfl⟩, ?_⟩
      rw [smul_neg, add_neg_cancel_right]
    obtain ⟨x, hx, w, ⟨t', rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hspan hu)
    refine ⟨x, hx, t' + t, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_add, add_assoc]

  let Xz : Submodule ℤ Y := X.restrictScalars ℤ
  let I : Ideal ℤ := Ideal.span {(R' : ℤ)}
  have hfg : (⊤ : Submodule ℤ (Y ⧸ Xz)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule ℤ (Y ⧸ Xz)) ≤ I • ⊤ := by
    intro m _
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective Xz m
    obtain ⟨x, hx, t, rfl⟩ := hdec b
    have hx' : Submodule.Quotient.mk (p := Xz) x = 0 :=
      (Submodule.Quotient.mk_eq_zero Xz).2 ((Submodule.restrictScalars_mem ℤ X x).2 hx)
    rw [Submodule.Quotient.mk_add, hx', zero_add, Submodule.Quotient.mk_smul, ← Nat.cast_smul_eq_nsmul ℤ]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ hfg hle
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton, zero_sub, dvd_neg] at hs1
    have h1 : ((R' : ℤ)) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg R') hs1
    omega
  have hsa : s • a ∈ X := by
    have h0 : s • Submodule.Quotient.mk (p := Xz) a = 0 := hs _ Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.restrictScalars_mem ℤ X _).1 h0
  refine ⟨s.natAbs, Int.natAbs_pos.2 hs0, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  rcases Int.natAbs_eq s with h | h
  · rw [← h]
    exact hsa
  · have : ((s.natAbs : ℤ)) = -s := by omega
    rw [this, neg_smul]
    exact X.neg_mem hsa

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem sum_cosetMin_ge_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  intro E _ _ cj hcj w₀ hw X _ _ _ Q β hβQ hQnn m hm n y hgen v hv q hq
  have hβpos : ∀ a, 0 ≤ (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβQ a]
    have h' : (0 : ℝ) ≤ Q a := by exact_mod_cast hQnn a
    linarith
  choose z hz using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.etPoint_min Q hQnn (y b) m
  have hgen' : ∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m • t := fun a => by
    obtain ⟨u, hu, t, ht⟩ := hgen a
    exact ⟨u, hu, m • t, by rw [ht, smul_smul, pow_two]⟩
  have hspan := Formalism.MainNotions.ModuliIntegralCharts.H1.etSpan_holds E X m hm n y z hgen'
  have hphi := Formalism.MainNotions.ModuliIntegralCharts.H1.phiCSpan_holds E cj hcj X w₀ hw β hβpos n (fun b => y b + m • z b) hspan
  have hsum : Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ ∑ b, (Q (y b + m • z b) : ℝ) := by
    refine hphi.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    have h := Formalism.MainNotions.ModuliIntegralCharts.H1.two_mul_form_half_unit hcj w₀ hw β (y b + m • z b)
    rw [hβQ] at h
    linarith
  have hpt : ∀ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤ v b := by
    intro b
    refine hv b _ fun z' => ?_
    have h : (Q (y b + m • z b) : ℚ) ≤ (Q (m • z' + y b) : ℚ) := by
      rw [add_comm (m • z')]
      exact_mod_cast hz b z'
    exact div_le_div_of_nonneg_right h (by positivity)
  have hR : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hqR : (q : ℝ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : ℝ) := by
    push_cast
    rw [← Finset.sum_div]
    exact hq.trans (div_le_div_of_nonneg_right hsum hR.le)
  have hqQ : q ≤ ∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) := by exact_mod_cast hqR
  calc ((q : ℚ) : WithTop ℚ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) :=
        WithTop.coe_le_coe.2 hqQ
    _ = ∑ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) := WithTop.coe_sum _ _
    _ ≤ ∑ b, v b := Finset.sum_le_sum fun b _ => hpt b

end GlobalTheory.EtaVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.le_sum_of_le_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  first | exact @GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq | exact GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq | (intros; apply GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq <;> assumption)
end
end
