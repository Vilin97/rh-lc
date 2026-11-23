module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMem
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZero

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem preimage_basicOpen_nonempty_of_mk_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}
    (i : X ⟶ PSpace K N) (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hne : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  by_contra hE
  apply hne
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.subset_span
  have hg' : g ∈ grK K N (e • 1) := by simpa using hg
  refine ⟨e, hg', fun j => ?_⟩
  have hy : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) e g hg' =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
  rw [hy, ← basicOpen_eq_bot_iff]
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hg he
  have h2 : X.basicOpen (evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) =
      i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
        (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) := by
    rw [Scheme.preimage_basicOpen]
    simp only [evV, Scheme.Hom.appLE_eq_app]
    rfl
  rw [h2, hb, eq_bot_iff]
  intro x hx
  exact hE ⟨x, hx.2⟩

end GlobalTheory.CompanionTheory.Geo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZeroStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.basic_open_nonempty_of_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsIntegral X → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}, 0 < e → ∀ (hg : g ∈ grK K N e), Ideal.Quotient.mk (homIdeal i) g ≠ 0 → ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | exact GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMemStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.homogeneous_ideal_component_mem : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first | exact @GlobalTheory.CompanionTheory.Geo.homIdeal_homog | exact GlobalTheory.CompanionTheory.Geo.homIdeal_homog | (intros; apply GlobalTheory.CompanionTheory.Geo.homIdeal_homog <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTop

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GeoNetop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem irrelevant_le_spanX (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hx
  rw [GradedRing.proj_apply] at h0
  have h1 : MvPolynomial.homogeneousComponent 0 x = 0 := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact h0
  rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero] at h1
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) h1
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hm0
  exact ⟨a, Set.mem_univ _, ha⟩

theorem exists_chart {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (x : X) :
    ∃ j : Fin (N + 1), x ∈ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) MvPolynomial.X
    (irrelevant_le_spanX K N)
  have hx : i x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X j) := by
    rw [h]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨j, hj⟩

theorem mk_C_mul_inv {K : Type} [Field K] {N : ℕ} (j : Fin (N + 1)) (c : K) (hc : c ≠ 0)
    (ha : MvPolynomial.C c ∈ grK K N (0 • 1)) (hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1)) :
    HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c) ha *
      HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c⁻¹) hb = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, Localization.mk_mul, ← map_mul, mul_inv_cancel₀ hc]

theorem constantCoeff_gen {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (hX : Nonempty X)
    {f : MvPolynomial (Fin (N + 1)) K} (d : ℕ) (hf : f ∈ grK K N (d • 1))
    (h0 : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    MvPolynomial.constantCoeff f = 0 := by
  have hc := MvPolynomial.homogeneousComponent_of_mem (m := 0) hf
  rw [MvPolynomial.homogeneousComponent_zero] at hc
  rw [MvPolynomial.constantCoeff_eq]
  by_cases hd : 0 = d • 1
  · rw [if_pos hd] at hc
    have hd0 : d = 0 := by simpa using hd.symm
    subst hd0
    obtain ⟨c, rfl⟩ : ∃ c, f = MvPolynomial.C c := ⟨_, hc.symm⟩
    rw [MvPolynomial.coeff_zero_C]
    by_contra hne
    obtain ⟨x⟩ := hX
    obtain ⟨j, hj⟩ := exists_chart i x
    haveI : Nonempty (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) := ⟨⟨x, hj⟩⟩
    haveI := Scheme.component_nontrivial X (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    have hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1) := by
      simpa using MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⁻¹
    have e := congrArg (evV i (MvPolynomial.X j) _ le_rfl) (mk_C_mul_inv j c hne hf hb)
    rw [map_mul, map_one, h0 j, zero_mul] at e
    exact zero_ne_one e
  · rw [if_neg hd, MvPolynomial.C_eq_zero] at hc
    exact hc

theorem homIdeal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N),
    Nonempty X → homIdeal i ≠ ⊤ := by
  intro K _ X N i hX htop
  have hle : homIdeal i ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) := by
    refine Ideal.span_le.2 ?_
    rintro f ⟨d, hf, h0⟩
    exact (RingHom.mem_ker).2 (constantCoeff_gen i hX d hf h0)
  have h1 : (1 : MvPolynomial (Fin (N + 1)) K) ∈ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) :=
    hle (htop ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1
end GlobalTheory.CompanionTheory.GeoNetop
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTopStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.homogeneous_ideal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), Nonempty X → homIdeal i ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | exact GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | (intros; apply GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PreimageBasicOpenNonempty

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

theorem homIdeal_homog : ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_component_mem ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_component_mem <;> assumption)

theorem homIdeal_ne_top [Nonempty X] : homIdeal i ≠ ⊤ := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_ne_top ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_ne_top <;> assumption)

theorem preimage_basicOpen_nonempty [IsIntegral X] {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hg0 : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first
    | exact GlobalTheory.T.basic_open_nonempty_of_ne_zero ..
    | (intros; apply GlobalTheory.T.basic_open_nonempty_of_ne_zero <;> assumption)

end CrystallineSemistableComparison.Pb
end
end
end
