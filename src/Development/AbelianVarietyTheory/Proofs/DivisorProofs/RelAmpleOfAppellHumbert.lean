module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunction
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSemicharactersNestedLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularOverlatticeRiemannForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfLiftTranslationFiniteIndexLatticesStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogeny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunctionStatement

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_section_of_appellHumbert_thetaFunction : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  first | exact @GlobalTheory.ThetaGAGA.exists_isFnPow | exact GlobalTheory.ThetaGAGA.exists_isFnPow | (intros; apply GlobalTheory.ThetaGAGA.exists_isFnPow <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularOverlatticeRiemannFormStatement

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_unimodular_overlattice_riemannForm : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (hermForm Hm l l').im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (Ef : LinearMap.BilinForm ℤ Λ₁) (N : ℕ), Λ ≤ Λ₁ ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧ (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
      Function.Bijective Ef ∧ 0 < N ∧ ∀ x ∈ Λ₁, N • x ∈ Λ := by
  first | exact @GlobalTheory.Overlattice.exists_unimodular_overlattice | exact GlobalTheory.Overlattice.exists_unimodular_overlattice | (intros; apply GlobalTheory.Overlattice.exists_unimodular_overlattice <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogenyStatement

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.theta_fourth_power_under_isogeny : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → (∀ θ, u.IsThetaFn Hm χ 4 θ → ∃ s, u.IsFnPow 4 s θ) →
    ∀ (P : Out.PolAV (Sp ℂ)) (u' : HolUnif P.A P.L g) (χ' : u'.Λ → ℂ) (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ),
    P.g = g → u'.IsAH Hm χ' →
    (∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im)) →
    ∃ ψ : A.left ⟶ P.A.left, ψ ≫ P.A.hom = A.hom ∧ (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) ∧
      ∀ x : A.left, ∃ (s : Out.H0 M 4) (V : P.A.left.Opens), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen V ∧
        Out.nonzeroLocus s = ψ ⁻¹ᵁ V := by
  first | exact @GlobalTheory.ThetaShift.exists_morphism_affine_cover | exact GlobalTheory.ThetaShift.exists_morphism_affine_cover | (intros; apply GlobalTheory.ThetaShift.exists_morphism_affine_cover <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections

abbrev PowSec {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (N : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (N : ℤ)))

def IsTrait {R₁ W : Type} [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W)
    (κ : FractionRing R₁ →+* FractionRing W) : Prop :=
  GlobalTheory.UU.CDVR W ∧ κ.comp (algebraMap R₁ (FractionRing R₁)) = (algebraMap W (FractionRing W)).comp ρ

section Frames

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G)


end Frames

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  (Xo : Moduli D l) {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Data

end GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleFramesIff

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FrameCompare
open GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections (PowSec)

variable {S : Scheme.{0}} (G : Over S)

variable [GrpObj G] [IsCommMonObj G] (L : RigLB G) (N : ℕ)


omit [GrpObj G] [IsCommMonObj G] in
theorem relAmple_iff {O : Type} [CommRing O] (b : S ⟶ Sp O) {A : LB S} (hA : A.IsLB) :
    (Out.RelAmple (Over.mk b) A →
      ∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) ∧
    (IsProper b → (∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧
      IsAffineOpen (Out.nonzeroLocus s)) → Out.RelAmple (Over.mk b) A) := by
  constructor
  · intro h z
    obtain ⟨n, hn, s, hs⟩ := (isAmpleLB_of_relAmple_of_isAffine (Over.mk b) hA h).exists_affine z
    obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := Fin 1) (e' := (n : ℤ)) rfl s
    exact ⟨n, s', hn, by rw [← e] at hs; exact hs⟩
  · intro hb h
    have : IsProper (Over.mk b).hom := hb
    have hc : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace b
    have ha : IsAmpleLB A := ⟨hA, hc, fun z => by
      obtain ⟨n, s, hn, hs⟩ := h z
      obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := PUnit) (e' := (n : ℤ)) rfl s
      exact ⟨n, hn, s', by rw [← e] at hs; exact hs⟩⟩
    refine relAmple_of_isAmpleLB (Over.mk b) hA fun U hU => ?_
    have : CompactSpace (b ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.1 (QuasiCompact.isCompact_preimage (f := b) _ U.isOpen hU.isCompact)
    exact ha.pull_of_isOpenImmersion (b ⁻¹ᵁ U).ι

end GlobalTheory.FrameCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbert

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LefschetzAmple

theorem relAmple_of_isAH : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → Out.RelAmple A M := by
  intro g A _ hA M u Hm χ hM hAH
  have hint : ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (hermForm Hm l l').im = n := by
    intro l hl l' hl'
    have h1 := GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l, hl⟩ ⟨l', hl'⟩
    have h2 := GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l', hl'⟩ ⟨l, hl⟩
    rw [add_comm] at h2
    have hsw := GlobalTheory.LatticeHom.hermForm_swap_of_isHermitian hAH.1 l l'
    have him : (hermForm Hm l' l).im = -(hermForm Hm l l').im := by
      rw [hsw, Complex.conj_im]
    have hne : χ ⟨l, hl⟩ * χ ⟨l', hl'⟩ ≠ 0 := by
      refine mul_ne_zero ?_ ?_ <;> refine norm_ne_zero_iff.1 ?_ <;> rw [hAH.2.2.1] <;> norm_num
    have h3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l l').im) =
        Complex.exp (Real.pi * Complex.I * (hermForm Hm l' l).im) := by
      refine mul_left_cancel₀ hne ?_
      rw [← h1, h2]
      ring
    rw [him] at h3
    have h4 : Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm l l').im) = 1 := by
      have e : (2 * Real.pi * Complex.I * (hermForm Hm l l').im : ℂ) =
          Real.pi * Complex.I * (hermForm Hm l l').im - Real.pi * Complex.I * ((-(hermForm Hm l l').im : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.exp_sub, h3, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h4
    refine ⟨n, ?_⟩
    have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_right_cancel₀ hπ (by rw [← hn]; ring : ((hermForm Hm l l').im : ℂ) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I))
    exact_mod_cast this
  obtain ⟨Λ₁, Ef, N, hle, hd1, hf1, hEf, hbij, hN, hNΛ⟩ := GlobalTheory.T.exists_unimodular_overlattice_riemannForm g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint
  obtain ⟨P, uB, χB, hg, hΛB, hAHB, -, -⟩ :=
    GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij
  have hle' : u.Λ ≤ uB.Λ := hΛB ▸ hle
  have hNΛ' : ∀ x ∈ uB.Λ, N • x ∈ u.Λ := hΛB ▸ hNΛ
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_shift_semicharacters_nested_lattices g u.Λ uB.Λ Hm χ χB hle' u.discrete u.full hAH.1 hAH.2.1 hAH.2.2.1 hAHB.2.2.1
    (GlobalTheory.LatticeHom.semicharacter_add u hM hAH) (GlobalTheory.LatticeHom.semicharacter_add uB P.isLB hAHB)
  obtain ⟨ψ, hψ, hψex, hcov⟩ := GlobalTheory.T.theta_fourth_power_under_isogeny g A hA M u Hm χ hM hAH (fun θ => GlobalTheory.T.exists_section_of_appellHumbert_thetaFunction g A hA M u Hm χ hM hAH 4 θ)
    P uB χB hle' a hg hAHB ha
  have hψa : IsAffineHom ψ := GlobalTheory.T.isAffineHom_of_lift_translation_finiteIndex_lattices g A hA P.A P.isAb M P.L u uB a N hN hle' hNΛ' ψ hψ hψex
  have : IsProper A.hom := hA.proper
  exact (GlobalTheory.FrameCompare.relAmple_iff A.hom hM).2 inferInstance fun x => by
    obtain ⟨s, V, hx, hV, hs⟩ := hcov x
    exact ⟨4, s, by norm_num, hx, hs ▸ hV.preimage ψ⟩

end GlobalTheory.LefschetzAmple
end
end
end
