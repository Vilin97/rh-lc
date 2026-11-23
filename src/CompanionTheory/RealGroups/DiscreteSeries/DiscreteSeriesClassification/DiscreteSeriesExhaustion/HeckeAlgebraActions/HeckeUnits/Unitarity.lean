module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.CommuteLeftRightCasimir
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.CompletePartialOrder
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeDualityFactsStatement
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.OmegaProjectionScalarCharacter

section

@[expose] public section

noncomputable section

open Finset Polynomial

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}


variable (X χ s) in
def toS (g : (step X (χ s)).V) : ↥(stepSub X (χ s)) := g

variable (X χ s) in
def ofS (g : ↥(stepSub X (χ s))) : (step X (χ s)).V := g

theorem toS_add (g g' : (step X (χ s)).V) : toS (X := X) (χ := χ) (s := s) (g + g') = toS (X := X) (χ := χ) (s := s) g + toS (X := X) (χ := χ) (s := s) g' := rfl

theorem toS_neg (g : (step X (χ s)).V) : toS (X := X) (χ := χ) (s := s) (-g) = -toS (X := X) (χ := χ) (s := s) g := rfl

theorem toS_sum (g : Fin (m + 1) → (step X (χ s)).V) : toS (X := X) (χ := χ) (s := s) (∑ c, g c) = ∑ c, toS (X := X) (χ := χ) (s := s) (g c) :=
  map_sum (AddMonoidHom.mk' (toS (X := X) (χ := χ) (s := s)) toS_add) g univ

theorem toS_E (a b : Fin (m + 1)) (g : (step X (χ s)).V) :
    ((toS (X := X) (χ := χ) (s := s) ((step X (χ s)).E a b g) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V) =
      tensE X a b (toS (X := X) (χ := χ) (s := s) g : Fin (m + 1) → X.V) := rfl

def coeY (G : Fin (m + 1) → (step X (χ s)).V) : Fin (m + 1) → Fin (m + 1) → X.V :=
  fun c => ((toS (X := X) (χ := χ) (s := s) (G c) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V)

theorem coeY_injective : Function.Injective (coeY (X := X) (χ := χ) (s := s)) := fun G G' h =>
  funext fun c => (Subtype.ext (congrFun h c) : toS (X := X) (χ := χ) (s := s) (G c) = toS (X := X) (χ := χ) (s := s) (G' c))

theorem coeY_smul (r : ℂ) (G) : coeY (X := X) (χ := χ) (s := s) (r • G) = r • coeY G := by
  funext c d; rfl

theorem coeY_sub (G G') : coeY (X := X) (χ := χ) (s := s) (G - G') = coeY G - coeY G' := by
  funext c d; rfl

theorem coe_omD (G : Fin (m + 1) → (step X (χ s)).V) :
    coeY (omD (step X (χ s)) G) = y2 (X := X) (coeY G) := by
  funext a
  have h : omD (step X (χ s)) G a = -∑ c, (step X (χ s)).E a c (G c) := by
    simp [omD, ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [show y2 (X := X) (coeY G) a = -∑ c, tensE X a c (coeY G c) by simp [y2, LinearMap.pi_apply]]
  change ((toS (X := X) (χ := χ) (s := s) (omD (step X (χ s)) G a) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V) = _
  rw [h, toS_neg, toS_sum, Submodule.coe_neg, Submodule.coe_sum]
  simp only [toS_E]
  rfl

theorem coe_pow (β : ℂ) (k : ℕ) (G : Fin (m + 1) → (step X (χ s)).V) :
    coeY (((omD (step X (χ s)) - β • 1) ^ k) G) = ((y2 (X := X) - β • 1) ^ k) (coeY G) := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, coeY_sub, coeY_smul, coe_omD]


variable (χ s) in
def phi0 (hS : ScalChar X χ) : X.V →ₗ[ℂ] (Fin (m + 1) → (step X (χ s)).V) where
  toFun v := fun c => ofS X χ s ⟨Pr X χ s (Pi.single c v), Pr_mem hS _⟩
  map_add' v w := by
    funext c
    show ofS X χ s ⟨Pr X χ s (Pi.single c (v + w)), _⟩ =
      ofS X χ s ⟨Pr X χ s (Pi.single c v), _⟩ + ofS X χ s ⟨Pr X χ s (Pi.single c w), _⟩
    apply Subtype.ext
    show Pr X χ s (Pi.single c (v + w)) = Pr X χ s (Pi.single c v) + Pr X χ s (Pi.single c w)
    rw [Pi.single_add, map_add (f := _)]
  map_smul' r v := by
    funext c
    show ofS X χ s ⟨Pr X χ s (Pi.single c (r • v)), _⟩ = r • ofS X χ s ⟨Pr X χ s (Pi.single c v), _⟩
    apply Subtype.ext
    show Pr X χ s (Pi.single c (r • v)) = r • Pr X χ s (Pi.single c v)
    rw [Pi.single_smul, map_smul]

theorem coe_projection_scalar_character (hS : ScalChar X χ) (v : X.V) : coeY (phi0 (X := X) (χ := χ) (s := s) hS v) = fun c => Pr X χ s (Pi.single c v) := by
  funext c; rfl

theorem omega_projection_scalar_character (hS : ScalChar X χ) (v : X.V) :
    omD (step X (χ s)) (phi0 (X := X) (χ := χ) (s := s) hS v) = (-(χ s + 1) - cn (m + 1)) • phi0 (X := X) (χ := χ) (s := s) hS v := by
  apply coeY_injective
  rw [coe_omD, coeY_smul, coe_projection_scalar_character]
  funext a
  have hy (H : Fin (m + 1) → Fin (m + 1) → X.V) (a : Fin (m + 1)) :
      y2 (X := X) H a = -∑ c, tensE X a c (H c) := by
    simp [y2, LinearMap.pi_apply]
  rw [hy]
  simp_rw [← Pr_tensE (X := X) (χ := χ) (s := s)]

  rw [← map_sum, sum_tensE_single, map_add (f := _), map_smul, Pr_om, om_Pr hS, ← add_smul, ← neg_smul, Pi.smul_apply]
  congr 1
  unfold cn; push_cast; ring

theorem tensVd_apply {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) (f : Fin n → M) (d : Fin n) :
    ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd E a b f d = E a b (f d) - if d = b then f a else 0 := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp

theorem tensE_single (a b d : Fin (m + 1)) (v : X.V) :
    tensE X a b (Pi.single d v) = Pi.single d (X.E a b v) + if b = d then Pi.single a v else 0 := by
  funext i
  rw [tensE_apply, Pi.add_apply]
  simp only [Pi.single_apply]
  by_cases hi : i = d <;> by_cases hb : b = d <;> by_cases ha : i = a <;> simp_all

end CompanionTheory.RgExh.Hk.UnitPf
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.RightCasimirMemSubmodule

section

@[expose] public section

noncomputable section

open Finset Polynomial

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem mem_of_eig' {M : Type*} [AddCommGroup M] [Module ℂ M] {T : Module.End ℂ M} {μ : ℂ} {f : M}
    (h : T f = μ • f) : f ∈ T.maxGenEigenspace μ :=
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 h)

variable (X) in
def Isub : Submodule ℂ (Fin (m + 1) → Fin (m + 1) → X.V) :=
  ⨆ k : ℕ, LinearMap.range ((y1 X ^ k) ∘ₗ eta X)

theorem mem_Isub (k : ℕ) (v : X.V) : (y1 X ^ k) (eta X v) ∈ Isub X :=
  Submodule.mem_iSup_of_mem k ⟨v, rfl⟩

theorem eta_mem_Isub (v : X.V) : eta X v ∈ Isub X := by
  simpa using mem_Isub (X := X) 0 v

theorem right_casimir_mem_submodule {H} (h : H ∈ Isub X) : y2 X H ∈ Isub X := by
  refine Submodule.iSup_induction _ (motive := fun H => y2 X H ∈ Isub X) h ?_ (by simp) ?_
  · rintro k _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← ((commute_left_right_casimir (X := X)).pow_left k).eq, Module.End.mul_apply, right_casimir_eta, map_neg,
      map_add, map_smul]
    refine neg_mem (add_mem ?_ (Submodule.smul_mem _ _ (mem_Isub k v)))
    have := mem_Isub (X := X) (k + 1) v
    rwa [pow_succ, Module.End.mul_apply] at this
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy


variable (X) in
def Om' : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) := y2 X + (eta X).comp (psi X)

theorem Om'_mem_Isub {H} (h : H ∈ Isub X) : Om' X H ∈ Isub X := by
  simp only [Om', LinearMap.add_apply, LinearMap.comp_apply]
  exact add_mem (right_casimir_mem_submodule h) (eta_mem_Isub _)

theorem Om'_pow_mem_Isub (k : ℕ) {H} (h : H ∈ Isub X) : (Om' X ^ k) H ∈ Isub X := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact Om'_mem_Isub ih

theorem aeval_mem_Isub (p : ℂ[X]) {H} (h : H ∈ Isub X) : aeval (Om' X) p H ∈ Isub X := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), LinearMap.add_apply]; exact add_mem hp hq
  | monomial k c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Om'_pow_mem_Isub k h)

theorem diff_mem_Isub (β : ℂ) (k : ℕ) (H) :
    ((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H ∈ Isub X := by
  induction k generalizing H with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    have e : (Om' X - β • 1) (((Om' X - β • 1) ^ k) H) - (y2 X - β • 1) (((y2 X - β • 1) ^ k) H) =
        (Om' X - β • 1) (((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H) +
          eta X (psi X (((y2 X - β • 1) ^ k) H)) := by
      simp only [map_sub, Om', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        Module.End.one_apply]
      abel
    rw [e]
    refine add_mem ?_ (eta_mem_Isub _)
    have hm := ih H
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact sub_mem (Om'_mem_Isub hm) (Submodule.smul_mem _ _ hm)

theorem left_casimir_pow_apply (k : ℕ) (H : Fin (m + 1) → Fin (m + 1) → X.V) (c : Fin (m + 1)) :
    (y1 X ^ k) H c = (om X ^ k) (H c) := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl

theorem Pr_om_pow (hS : ScalChar X χ) (k : ℕ) (f : Fin (m + 1) → X.V) :
    Pr X χ s ((om X ^ k) f) = (χ s - cn (m + 1)) ^ k • Pr X χ s f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, Pr_om, ih, map_smul, om_Pr hS, smul_smul, pow_succ]

theorem Pr_Isub (hS : ScalChar X χ) {H} (h : H ∈ Isub X) :
    ∃ v : X.V, ∀ c, Pr X χ s (H c) = Pr X χ s (Pi.single c v) := by
  refine Submodule.iSup_induction _ (motive := fun H => ∃ v : X.V, ∀ c, Pr X χ s (H c) = Pr X χ s (Pi.single c v))
    h ?_ ⟨0, by simp⟩ ?_
  · rintro k _ ⟨v, rfl⟩
    refine ⟨(χ s - cn (m + 1)) ^ k • v, fun c => ?_⟩
    simp only [LinearMap.comp_apply, left_casimir_pow_apply, eta_apply, Pr_om_pow hS, Pi.single_smul, map_smul]
  · rintro x y ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v + w, fun c => by rw [Pi.add_apply, map_add (f := _), hv, hw, Pi.single_add, map_add (f := _)]⟩

end CompanionTheory.RgExh.Hk.UnitPf
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnits.Unitarity

section

@[expose] public section

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk.UnitB

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk.UnitPf

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem Om'_CH (K : ℕ)
    (hK : ((List.ofFn fun t : Fin (m + 1) =>
      omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))).prod) ^ K = 0) :
    ((List.ofFn fun t : Fin (m + 1) =>
      Om' X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V))).prod) ^ K = 0 := by
  have e : (fun t : Fin (m + 1) =>
      Om' X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V))) =
      (liftR (X := X)) ∘ (fun t : Fin (m + 1) =>
        omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))) := by
    funext t
    simp only [Function.comp_apply, map_sub, liftR_smul_one, omegaP_eq]
    rfl
  rw [e, ← List.map_ofFn, ← map_list_prod, ← map_pow, hK, map_zero]

theorem aeval_CH (K : ℕ) (γ : Fin (m + 1) → ℂ) (T : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V)) :
    Polynomial.aeval T (((List.ofFn fun t : Fin (m + 1) => Polynomial.X - Polynomial.C (γ t)).prod) ^ K) =
      ((List.ofFn fun t : Fin (m + 1) => T - γ t • (1 : Module.End ℂ _)).prod) ^ K := by
  rw [map_pow, map_list_prod, List.map_ofFn]
  congr 3
  funext t
  simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one]

theorem aeval_lin (k : ℕ) (β : ℂ) (T : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V)) :
    Polynomial.aeval T ((Polynomial.X - Polynomial.C β) ^ k) = (T - β • (1 : Module.End ℂ _)) ^ k := by
  simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem cop (γ : Fin (m + 1) → ℂ) (β : ℂ) (h : ∀ t, γ t ≠ β) (K k : ℕ) :
    IsCoprime (((List.ofFn fun t : Fin (m + 1) => Polynomial.X - Polynomial.C (γ t)).prod) ^ K)
      ((Polynomial.X - Polynomial.C β) ^ k) := by
  refine IsCoprime.pow ?_
  rw [List.prod_ofFn]
  exact IsCoprime.prod_left fun t _ =>
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 (h t)).isUnit

theorem coeY_mem_Isub
    (hD : ∃ K : ℕ, ((List.ofFn fun t : Fin (m + 1) =>
      omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))).prod) ^ K = 0)
    (hfree : ∀ r, χ r ≠ χ s + 1) (G : Fin (m + 1) → (step X (χ s)).V)
    (hG : G ∈ backSub (step X (χ s)) (χ s + 1)) : coeY G ∈ Isub X := by
  obtain ⟨K, hK⟩ := hD
  rw [backSub, Module.End.mem_maxGenEigenspace] at hG
  obtain ⟨k, hk⟩ := hG
  have h0 : ((y2 X - (-(χ s + 1) - cn (m + 1)) • 1) ^ k) (coeY G) = 0 := by
    rw [← coe_pow, hk]; rfl
  have hI : ((Om' X - (-(χ s + 1) - cn (m + 1)) • 1) ^ k) (coeY G) ∈ Isub X := by
    have := diff_mem_Isub (X := X) (-(χ s + 1) - cn (m + 1)) k (coeY G)
    rwa [h0, sub_zero] at this
  obtain ⟨A, B, hAB⟩ := cop (fun t => -χ t - cn (m + 1)) (-(χ s + 1) - cn (m + 1))
    (fun t h => hfree t (by linear_combination -h)) K k
  have e := congrArg (fun q => Polynomial.aeval (Om' X) q (coeY G)) hAB
  simp only [map_add (f := _), map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply] at e
  rw [← e, aeval_CH, Om'_CH K hK, LinearMap.zero_apply, map_zero, zero_add, aeval_lin]
  exact aeval_mem_Isub B hI


variable (χ s) in
def phiB (hS : ScalChar X χ) : X.V →ₗ[ℂ] ↥(backSub (step X (χ s)) (χ s + 1)) :=
  (phi0 χ s hS).codRestrict (backSub (step X (χ s)) (χ s + 1)) fun v => mem_of_eig' (omega_projection_scalar_character hS v)

theorem phiB_inj (hS : ScalChar X χ) (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) (hfree : ∀ r, χ r ≠ χ s + 1) :
    Function.Injective (phiB χ s hS) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv' : phi0 χ s hS v = 0 := congrArg Subtype.val hv
  have h := ptr_Pr (X := X) (s := s) hS v
  have h0 : ∑ c, Pr X χ s (Pi.single c v) c = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have hc : Pr X χ s (Pi.single c v) = 0 := congrArg (fun G => coeY G c) hv'
    rw [hc]; rfl
  rw [h0] at h
  have hne : (kap χ s)⁻¹ * -capP χ (-χ s - 1) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (kap_ne hsimp)) (neg_ne_zero.2 (capelliPoly_ne hfree))
  exact (smul_eq_zero.1 h.symm).resolve_left hne

theorem phiB_surj (hS : ScalChar X χ) (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) (hfree : ∀ r, χ r ≠ χ s + 1)
    (hom : ∀ f ∈ stepSub X (χ s), om X f = (χ s - cn (m + 1)) • f)
    (hD : ∃ K : ℕ, ((List.ofFn fun t : Fin (m + 1) =>
      omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))).prod) ^ K = 0) :
    Function.Surjective (phiB χ s hS) := by
  rintro ⟨G, hG⟩
  obtain ⟨v, hv⟩ := Pr_Isub (s := s) hS (coeY_mem_Isub hD hfree G hG)
  refine ⟨v, Subtype.ext (coeY_injective (funext fun c => ?_))⟩
  change Pr X χ s (Pi.single c v) = coeY G c
  rw [← hv c]
  exact Pr_step hS hsimp _ (hom _ (show ↥(stepSub X (χ s)) from G c).2)


variable (χ s) in
def phiBk (hS : ScalChar X χ) (hB : BackStable) :
    X.V →ₗ[ℂ] (back (step X (χ s)) (χ s + 1) (hB (m + 1) _ _)).V := phiB χ s hS

theorem coeY_tensVd (G : Fin (m + 1) → (step X (χ s)).V) (a b : Fin (m + 1)) :
    coeY (X := X) (χ := χ) (s := s) (ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd (step X (χ s)).E a b G) =
      fun c => tensE X a b (coeY G c) - if c = b then coeY G a else 0 := by
  funext c
  unfold coeY
  rw [tensVd_apply]
  split_ifs <;> rfl

theorem phiB_E (hS : ScalChar X χ) (hB : BackStable) (a b : Fin (m + 1)) (v : X.V) :
    phiBk χ s hS hB (X.E a b v) = (back (step X (χ s)) (χ s + 1) (hB (m + 1) _ _)).E a b (phiBk χ s hS hB v) := by
  apply Subtype.ext
  apply coeY_injective (X := X) (χ := χ) (s := s)
  funext c
  change coeY (phi0 χ s hS (X.E a b v)) c =
    coeY (ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd (step X (χ s)).E a b (phi0 χ s hS v)) c
  rw [coeY_tensVd, coe_projection_scalar_character, coe_projection_scalar_character]
  dsimp only
  by_cases h : c = b
  · subst h
    rw [if_pos rfl, ← Pr_tensE, tensE_single, if_pos rfl, map_add (f := _), add_sub_cancel_right]
  · rw [if_neg h, sub_zero, ← Pr_tensE, tensE_single, if_neg (Ne.symm h), add_zero]

theorem unit_of_dualFacts (hDF : DualFacts) : Unit := by
  rintro (_ | m) X χ s hB hS hfree hsimp hom
  · exact s.elim0
  · have hH : HasChar X χ := ⟨1, fun Y => by rw [hS Y, sub_self, pow_one]⟩
    have hD := (hDF (m + 1) X χ hH).1
    obtain ⟨φ, hφ⟩ : ∃ φ : X.V ≃ₗ[ℂ] (back (step X (χ s)) (χ s + 1) (hB (m + 1) _ _)).V,
        ∀ v, φ v = phiBk χ s hS hB v :=
      ⟨LinearEquiv.ofBijective (phiBk χ s hS hB) ⟨phiB_inj hS hsimp hfree, phiB_surj hS hsimp hfree hom hD⟩,
        fun v => rfl⟩
    refine ⟨φ.symm, fun a b x => φ.injective ?_⟩
    rw [LinearEquiv.apply_symm_apply, hφ, phiB_E hS hB a b, ← hφ, LinearEquiv.apply_symm_apply]

end CompanionTheory.RgExh.Hk.UnitB

theorem unitarity : CompanionTheory.RgExh.Hk.Unit := CompanionTheory.RgExh.Hk.UnitB.unit_of_dualFacts GlobalTheory.T.HeckeDualityFacts
end
end
end
