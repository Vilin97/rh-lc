module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerDifferentialsFreeCoordinateFormsAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrame

section

@[expose] public section

set_option autoImplicit false

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.CechPer

theorem sum_symm_smul_wedge_eq_zero {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (ω : Fin g → Ω[B⁄ℂ]) (S : Fin g → Fin g → B) (hS : ∀ a b, S a b = S b a) :
    ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) = 0 := by
  set X := ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) with hX
  have h1 : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    rw [hX, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [wedge_swap (ω c) (ω b), hS c b, smul_neg]
  have h2 : (2 : B) • X = 0 := by
    rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr h1
  have h3 : algebraMap ℂ B (2⁻¹) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ B) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc X = (algebraMap ℂ B (2⁻¹) * 2) • X := by rw [h3, one_smul]
    _ = 0 := by rw [mul_smul, h2, smul_zero]

theorem dOne_eq_sum_of_frame {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ])
    (hc : ∀ a b x, d a (d b x) = d b (d a x))
    (hf : ∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) (ξ : Ω[B⁄ℂ]) :
    dOne ℂ B ξ = ∑ b, ∑ c, d b ((d c).liftKaehlerDifferential ξ) • wedge ℂ B (ω b) (ω c) := by
  induction ξ using ind1 with
  | h0 => simp
  | ha x y hx hy =>
    rw [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_add (f := _), map_add (f := _), add_smul]
  | h x y =>
    have hD : ∀ z : B, D ℂ B z = ∑ a, d a z • ω a := fun z ↦ by
      simpa only [Derivation.liftKaehlerDifferential_comp_D] using hf (D ℂ B z)
    have h0 := sum_symm_smul_wedge_eq_zero ω (fun b c ↦ x * d b (d c y))
      (fun a b ↦ by rw [hc a b])
    have h1 : wedge ℂ B (D ℂ B x) (D ℂ B y) =
        ∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c) := by
      rw [hD x, hD y, LinearMap.map_sum₂]
      refine Finset.sum_congr rfl fun b _ ↦ ?_

      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [map_smul, LinearMap.map_smul₂, mul_smul]
    rw [dOne_smul_D, h1, ← zero_add (∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c)), ← h0,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul, add_smul]

theorem dOne_eq_zero_of_frame_of_symm : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  intro B _ _ g d ω hc hd hf k hk
  have hl : ∀ c, (d c).liftKaehlerDifferential (∑ a, k a • ω a) = k c := fun c ↦ by

    simp [map_sum, hd]
  rw [dOne_eq_sum_of_frame d ω hc hf]
  simp only [hl]
  exact sum_symm_smul_wedge_eq_zero ω (fun b c ↦ d b (k c)) hk

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrameStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  first | exact @GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | exact GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | (intros; apply GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformised

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem clm_eq_sum_single_smul_proj {g : ℕ} (f : (Fin g → ℂ) →L[ℂ] ℂ) :
    f = ∑ a, f (Pi.single a 1) • (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  conv_lhs => rw [pi_eq_sum_univ' v]

  simp [map_sum, mul_comm]

theorem fderiv_partial_symm {g : ℕ} {s : Set (Fin g → ℂ)} (hs : IsOpen s) {h : (Fin g → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h s) {k : Fin g → (Fin g → ℂ) → ℂ} (hk : ∀ a, DifferentiableOn ℂ (k a) s)
    (e : ∀ a, ∀ z ∈ s, fderiv ℂ h z (Pi.single a 1) = k a z) (a b : Fin g) {z : Fin g → ℂ} (hz : z ∈ s) :
    fderiv ℂ (k b) z (Pi.single a 1) = fderiv ℂ (k a) z (Pi.single b 1) := by
  have hn : s ∈ 𝓝 z := hs.mem_nhds hz
  have h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt h (fderiv ℂ h y) y := by
    filter_upwards [hn] with y hy using (hh.differentiableAt (hs.mem_nhds hy)).hasFDerivAt
  have h2 : fderiv ℂ h =ᶠ[𝓝 z]
      fun y ↦ ∑ c, k c y • (ContinuousLinearMap.proj c : (Fin g → ℂ) →L[ℂ] ℂ) := by
    filter_upwards [hn] with y hy
    rw [clm_eq_sum_single_smul_proj (fderiv ℂ h y)]
    exact Finset.sum_congr rfl fun c _ ↦ by rw [e c y hy]
  have h3 : DifferentiableAt ℂ (fderiv ℂ h) z := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h2
    exact DifferentiableAt.fun_sum fun c _ ↦ ((hk c).differentiableAt hn).smul_const _
  have h4 : ∀ c v, fderiv ℂ (k c) z v = fderiv ℂ (fderiv ℂ h) z v (Pi.single c 1) := by
    intro c v
    have h5 : k c =ᶠ[𝓝 z] fun y ↦ fderiv ℂ h y (Pi.single c 1) := by
      filter_upwards [hn] with y hy using (e c y hy).symm
    rw [h5.fderiv_eq, fderiv_clm_apply h3 (differentiableAt_const _)]
    simp
  rw [h4, h4]
  exact second_derivative_symmetric_of_eventually h1 h3.hasFDerivAt _ _

theorem exists_closed_form_fderiv_eq (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g)
    (hA : IsAbelianScheme A) (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ) (hh : DifferentiableOn ℂ h (pre u.ex U.1))
    (hr : ∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) :
    ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  obtain ⟨hop, hdiff, -, -, -, -, -, -, -, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨d, ω, hcomm, hd, hdual, hspan, hev⟩ := GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian A g L u hA U
  choose k₀ hk₀ using hr
  let k : Fin g → Sec (str A) U.1 := k₀
  have hk : ∀ a, ∀ z ∈ pre u.ex U.1, fderiv ℂ h z (Pi.single a 1) = val u.ex U.1 (k a) z := hk₀
  refine ⟨∑ a, k a • ω a, GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame _ g d ω hcomm hdual hspan k fun a b ↦ ?_, fun z hz ↦ ?_⟩
  · have h0 : d a (k b) - d b (k a) = 0 := by
      refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U.1 _ fun z hz ↦ ?_
      obtain ⟨e, he⟩ := halg U.1 z hz
      have h1 := he (d a (k b) - d b (k a))
      rw [map_sub, ← he (d a (k b)), ← he (d b (k a)), hd a _ z hz, hd b _ z hz,
        fderiv_partial_symm (hop U.1) hh (fun c ↦ hdiff U.1 (k c)) hk a b hz, sub_self] at h1
      exact h1
    exact sub_eq_zero.mp h0
  · rw [clm_eq_sum_single_smul_proj (fderiv ℂ h z), clm_eq_sum_single_smul_proj (evForm u.ex U.1 z _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have h1 : (d a).liftKaehlerDifferential (∑ c, k c • ω c) = k a := by

      simp [map_sum, hdual]
    rw [hev a _ z hz, h1, hk a z hz]

end GlobalTheory.CechPer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformisedStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ), DifferentiableOn ℂ h (pre u.ex U.1) → (∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) → ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  first | exact @GlobalTheory.CechPer.exists_closed_form_fderiv_eq | exact GlobalTheory.CechPer.exists_closed_form_fderiv_eq | (intros; apply GlobalTheory.CechPer.exists_closed_form_fderiv_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctions

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem exists_isPer_of_quasiPeriodic : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ U, DifferentiableOn ℂ (k U) (pre u.ex U.1)) → (∀ U V : A.left.affineOpens, V ≤ U → IsReg u.ex V.1 (k V - k U)) → (∀ U a, IsReg u.ex U.1 fun z => fderiv ℂ (k U) z (Pi.single a 1)) → (∀ U (l : u.Λ), ∀ z ∈ pre u.ex U.1, k U (z + l) = k U z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  intro A _ g L u hA k q hk hreg hder hper
  obtain ⟨hopen, hdiff, -, -, -, hmono, -, -, hres, hev, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have hf : ∀ (U V : A.left.affineOpens) (_ : Opposite.op U ⟶ Opposite.op V), ∃ b : Sec (str A) V.1,
      ∀ z ∈ pre u.ex V.1, (k V - k U) z = val u.ex V.1 b z :=
    fun U V a => hreg U V (leOfHom a.unop)
  choose f hf using hf
  have hω : ∀ U : A.left.affineOpens, ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧
      ∀ z ∈ pre u.ex U.1, fderiv ℂ (k U) z = evForm u.ex U.1 z ξ :=
    fun U => GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised A g L u hA U (k U) (hk U) (hder U)
  choose ω hωc hωe using hω
  have hsub : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_sub e b b').trans (congrArg₂ (· - ·) (he b).symm (he b').symm))
  have hadd : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_add e b b').trans (congrArg₂ (· + ·) (he b).symm (he b').symm))
  have hfun : ∀ (U V W : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V) (ψ : Opposite.op V ⟶ Opposite.op W),
      f U W (φ ≫ ψ) = Sec.res (str A) (show W.1 ≤ V.1 from leOfHom ψ.unop) (f U V φ) + f V W ψ := by
    intro U V W φ ψ
    have hle : W.1 ≤ V.1 := leOfHom ψ.unop
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA W.1
      (f U W (φ ≫ ψ) - (Sec.res (str A) hle (f U V φ) + f V W ψ) : Sec (str A) W.1) fun z hz => ?_)
    have e1 := hsub W.1 (f U W (φ ≫ ψ)) (Sec.res (str A) hle (f U V φ) + f V W ψ) z hz
    have e2 := hadd W.1 (Sec.res (str A) hle (f U V φ)) (f V W ψ) z hz
    have e3 := hres V.1 W.1 hle (f U V φ) z hz
    have e4 := hf U W (φ ≫ ψ) z hz
    have e5 := hf U V φ z (hmono _ _ hle hz)
    have e6 := hf V W ψ z hz
    simp only [Pi.sub_apply] at e4 e5 e6
    linear_combination e1 - e2 - e3 - e4 + e5 + e6
  have hform : ∀ (U V : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V),
      ω V = p1 (OAff (str A)) φ (ω U) + KaehlerDifferential.D ℂ (Sec (str A) V.1) (f U V φ) := by
    intro U V φ
    refine sub_eq_zero.1 (GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values A g L u hA V _ fun z hz => ?_)
    have hle : V.1 ≤ U.1 := leOfHom φ.unop
    have hz' : z ∈ pre u.ex U.1 := hmono _ _ hle hz
    have e1 := GlobalTheory.T.evForm_restriction_eq A g L u U V φ (ω U) z hz
    have e2 := (GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz).2.2 (f U V φ)
    have heq : k V =ᶠ[nhds z] k U + val u.ex V.1 (f U V φ) := by
      filter_upwards [(hopen _).mem_nhds hz] with w hw
      have := hf U V φ w hw
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply]
      linear_combination this
    have e3 : fderiv ℂ (k V) z = fderiv ℂ (k U) z + fderiv ℂ (val u.ex V.1 (f U V φ)) z :=
      heq.fderiv_eq.trans (fderiv_add ((hk _).differentiableAt ((hopen _).mem_nhds hz'))
        ((hdiff _ _).differentiableAt ((hopen _).mem_nhds hz)))
    refine (map_sub (evForm u.ex V.1 z) _ _).trans (sub_eq_zero.2 ?_)
    refine Eq.trans ?_ (map_add (evForm u.ex V.1 z) _ _).symm
    exact (hωe V z hz).symm.trans (e3.trans (congrArg₂ (· + ·) ((hωe U z hz').trans e1.symm) e2.symm))
  let c0 : Tot1 (OAff (str A)) := (fun U V a => f U.unop V.unop a, fun U => ω U.unop)
  have hc : c0 ∈ cechDeRhamTotalCocyclesOne (OAff (str A)) :=
    mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨fun T T' T'' φ ψ => hfun T.unop T'.unop T''.unop φ ψ, fun T T' φ => hform T.unop T'.unop φ,
      fun T => hωc T.unop⟩
  refine ⟨Hyp1.mk _ ⟨c0, hc⟩, ⟨c0, hc⟩, k, rfl, ⟨hk, fun U V a z hz => ?_, fun U z hz => hωe U z hz⟩, hper⟩
  have := hf U V a z hz
  simp only [Pi.sub_apply] at this
  change k V z = k U z + val u.ex V.1 (f U V a) z
  linear_combination this

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctionsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cechDeRham_class_of_quasiPeriodic_functions : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ U, DifferentiableOn ℂ (k U) (pre u.ex U.1)) → (∀ U V : A.left.affineOpens, V ≤ U → IsReg u.ex V.1 (k V - k U)) → (∀ U a, IsReg u.ex U.1 fun z => fderiv ℂ (k U) z (Pi.single a 1)) → (∀ U (l : u.Λ), ∀ z ∈ pre u.ex U.1, k U (z + l) = k U z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  first | exact @GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic | exact GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic | (intros; apply GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic <;> assumption)
end
end
