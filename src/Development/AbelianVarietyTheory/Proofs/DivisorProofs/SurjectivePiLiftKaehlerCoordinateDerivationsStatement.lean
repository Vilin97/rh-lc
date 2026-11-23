module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivRegularFunctionsAffineOpen

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPerImm

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), IsAffineOpen U → ∀ z ∈ pre u.ex U, ∀ w : Fin g → ℂ, (∀ b : Γ(A.left, U), fderiv ℂ (val u.ex U b) z w = 0) → w = 0 := by
  intro A _ g L u _ U hU z hz w hw
  refine GlobalTheory.HolUnifSec.eq_zero_of_fderiv_eq_zero u z w fun O f hO => ?_
  have hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := hz
  have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ O ⊓ U :=
    (GlobalTheory.top_le_preimage_iff_mem _ _).1 ((GlobalTheory.top_le_preimage_inf _ O U).2 ⟨hO, hzU⟩)
  obtain ⟨r, hrle, hrmem⟩ := hU.exists_basicOpen_le (V := O ⊓ U) ⟨_, hmem⟩ hmem.2
  have hDO : A.left.basicOpen r ≤ O := hrle.trans inf_le_left
  have hDU : A.left.basicOpen r ≤ U := A.left.basicOpen_le r
  letI := (A.left.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen r
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj r (resG A.left hDO f)
  let P : Set (Fin g → ℂ) := {y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ A.left.basicOpen r}
  have hP : IsOpen P := (u.hol _ 0).1
  have hzP : z ∈ P := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hrmem
  set F := fun y => valAt' (u.ex y).left O f
  set R := fun y => valAt' (u.ex y).left U r
  set B := fun y => valAt' (u.ex y).left U b
  have key : ∀ y ∈ P, F y * R y ^ n = B y := by
    intro y hy
    have h1 := congrArg (valAt' (u.ex y).left (A.left.basicOpen r)) hb
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hy] at h1
    have e1 : valAt' (u.ex y).left (A.left.basicOpen r) (resG A.left hDO f) = F y := GlobalTheory.valAt'_res _ hDO f hy
    have e2 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ r) = R y := GlobalTheory.valAt'_res _ hDU r hy
    have e3 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ b) = B y := GlobalTheory.valAt'_res _ hDU b hy
    rw [e1, e2, e3] at h1
    exact h1
  have hpreO : IsOpen {y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ O} := (u.hol O f).1
  have hF : HasFDerivAt F (fderiv ℂ F z) z :=
    (((u.hol O f).2 z hO).differentiableAt (hpreO.mem_nhds hO)).hasFDerivAt
  have hR : HasFDerivAt R (fderiv ℂ R z) z :=
    (((u.hol U r).2 z hzU).differentiableAt ((u.hol U r).1.mem_nhds hzU)).hasFDerivAt
  have hB : HasFDerivAt B (fderiv ℂ B z) z :=
    (((u.hol U b).2 z hzU).differentiableAt ((u.hol U b).1.mem_nhds hzU)).hasFDerivAt
  have hFR := hF.mul (hR.pow n)
  have hev : (fun y => F y * R y ^ n) =ᶠ[nhds z] B :=
    Filter.eventually_of_mem (hP.mem_nhds hzP) key
  have hB' := hFR.congr_of_eventuallyEq hev.symm
  have e := congrArg (fun T : (Fin g → ℂ) →L[ℂ] ℂ => T w) (hB'.unique hB)
  have hRw : fderiv ℂ R z w = 0 := hw r
  have hBw : fderiv ℂ B z w = 0 := hw b
  have hRz : R z ≠ 0 := (GlobalTheory.top_le_preimage_basicOpen_iff _ U r).1 hzP
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hRw, hBw, smul_zero, smul_eq_mul,
    mul_zero, zero_add] at e
  exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hRz)

end GlobalTheory.CechPerImm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivRegularFunctionsAffineOpenStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_zero_of_fderiv_regular_functions_affineOpen : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), IsAffineOpen U → ∀ z ∈ pre u.ex U, ∀ w : Fin g → ℂ, (∀ b : Γ(A.left, U), fderiv ℂ (val u.ex U b) z w = 0) → w = 0 := by
  first | exact @GlobalTheory.CechPerImm.main | exact GlobalTheory.CechPerImm.main | (intros; apply GlobalTheory.CechPerImm.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePiLiftKaehlerCoordinateDerivations

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem surjective_pi_liftKaehler_of_pointwise {K B J : Type*} [Field K] [CommRing B] [Algebra K B] [Fintype J] [DecidableEq J]
    (d : J → Derivation K B B)
    (h : ∀ m : Ideal B, m.IsMaximal → ∃ e : B →ₐ[K] K, (∀ b, e b = 0 → b ∈ m) ∧
      ∀ w : J → K, (∀ x, ∑ a, e (d a x) * w a = 0) → w = 0) :
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  rw [← LinearMap.range_eq_top]
  by_contra hN
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom
    (LinearMap.range (LinearMap.pi fun a => (d a).liftKaehlerDifferential))).resolve_left hN
  have hs : IsSimpleModule B ((J → B) ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
  obtain ⟨e, he, hw⟩ := h (Module.annihilator B ((J → B) ⧸ M)) IsSimpleModule.annihilator_isMaximal
  let φ : B →ₗ[K] (J → K) := LinearMap.pi fun a => e.toLinearMap ∘ₗ (d a).toLinearMap
  have hφ : LinearMap.range φ = ⊤ := by
    by_contra hφ
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hφ)
    have hfy : ∀ y : J → K, f y = ∑ a, y a * f (Pi.single a 1) := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ' y]

      simp [map_sum]
    have h0 := hw (fun a => f (Pi.single a 1)) fun x => by
      have : f (φ x) = 0 := hf ⟨x, rfl⟩
      rw [hfy] at this
      exact this
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [hfy]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [congrFun h0 a]
    simp
  apply hM.1
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 hφ fun a => e (y a)
  have h1 : (fun a => d a x) ∈ M := by
    refine hle ⟨KaehlerDifferential.D K B x, ?_⟩
    funext a
    simp
  have h2 : y - (fun a => d a x) ∈ M := by
    rw [pi_eq_sum_univ' (y - fun a => d a x)]
    refine M.sum_mem fun a _ => ?_
    have hm : (y - fun a => d a x) a ∈ Module.annihilator B ((J → B) ⧸ M) := by
      apply he
      have : e (d a x) = e (y a) := congrFun hx a
      simp [this]
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hm _
  simpa using M.add_mem h2 h1

theorem surjective_pi_liftKaehler_coord : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (U : A.left.affineOpens) (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)),
    (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) →
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  intro A _ g L u hA U d hd
  refine surjective_pi_liftKaehler_of_pointwise d fun m hm => ?_
  obtain ⟨z, hz, hm'⟩ := GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA U.1 U.2 m hm
  obtain ⟨e, he⟩ := (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz
  refine ⟨e, fun b hb => (hm' b).2 ((he b).trans hb), fun w hw => ?_⟩
  refine GlobalTheory.T.eq_zero_of_fderiv_regular_functions_affineOpen A g L u hA U.1 U.2 z hz w fun b => ?_
  rw [← hw b]
  conv_lhs => rw [pi_eq_sum_univ' w]

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  exact congrArg (· * w a) ((hd a b z hz).symm.trans (he _))

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePiLiftKaehlerCoordinateDerivationsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.surjective_pi_liftKaehler_coordinateDerivations : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)), (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) → Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  first | exact @GlobalTheory.CechPer.surjective_pi_liftKaehler_coord | exact GlobalTheory.CechPer.surjective_pi_liftKaehler_coord | (intros; apply GlobalTheory.CechPer.surjective_pi_liftKaehler_coord <;> assumption)
end
end
