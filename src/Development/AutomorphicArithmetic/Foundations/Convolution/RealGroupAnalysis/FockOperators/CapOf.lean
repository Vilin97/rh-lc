module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapAbs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
public import Mathlib.Algebra.BigOperators.Fin
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.EopLift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockOps
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LiftNegForm
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XaCommCoord
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LiftLin
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Capelli

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capelli :
    ∀ (A : Type) [Ring A] (X D a : Fin 2 → Fin 2 → A) (q Δ h : A), (∀ i j k l, X i j * X k l = X k l * X i j) → (∀ i j k l, D i j * D k l = D k l * D i j) →
    (∀ i j k l, D i j * X k l = X k l * D i j + if i = k ∧ j = l then 1 else 0) →
    (∀ i j, a i j = -(if i = j then 1 else 0) - ∑ b, X j b * D i b) → q = X 0 1 * X 1 0 - X 0 0 * X 1 1 → Δ = D 0 1 * D 1 0 - D 0 0 * D 1 1 →
    h = (∑ i, ∑ j, X i j * D i j) + 2 →
    Δ * q - q * Δ = h ∧ a 0 0 + a 1 1 = -h ∧
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h - 2 * (q * Δ + Δ * q) := by
  intro A _ X D a q Δ h hX hD hDX ha hq hΔ hh
  have hDX' : ∀ i j k l z, D i j * (X k l * z) = X k l * (D i j * z) + if i = k ∧ j = l then z else 0 := by
    intro i j k l z
    rw [← mul_assoc, hDX, add_mul, mul_assoc]
    split_ifs <;> simp
  have hX' : ∀ i j k l z, X i j * (X k l * z) = X k l * (X i j * z) := by
    intro i j k l z
    rw [← mul_assoc, hX, mul_assoc]
  have h2 : (2 : A) = 1 + 1 := by norm_num
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  subst hq hΔ hh
  simp only [ha, Fin.sum_univ_two, h2, h01, h10, if_true, if_false]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    try simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_zero, zero_sub, neg_neg, mul_one, one_mul, mul_assoc, hDX, hDX', h01, h10, and_self, and_true, true_and, and_false, false_and, if_true, if_false, add_zero,
      hX 1 1 0 0, hX 1 1 0 1, hX 1 1 1 0, hX 1 0 0 0, hX 1 0 0 1, hX 0 1 0 0,
      hX' 1 1 0 0, hX' 1 1 0 1, hX' 1 1 1 0, hX' 1 0 0 0, hX' 1 0 0 1, hX' 0 1 0 0,
      hD 1 1 0 0, hD 1 1 0 1, hD 1 1 1 0, hD 1 0 0 0, hD 1 0 0 1, hD 0 1 0 0]
  all_goals abel
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapLam

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capLam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F) (Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2), (∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ) → LieLift O W M π → MoveE O W M π →
    ∀ (τ : E →+* ℂ) u, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, cap τ u (Λ f φ) = Λ (TR.cap (pl F τ) u f) φ := by
  intro F E _ _ _ _ _ _ _ D W M π O Λ hΛ hL hE τ u f hf φ hφ
  obtain ⟨hXX, hDD, hDX, he, hfo, hh⟩ := weylX F E D W O τ
  obtain ⟨c1, c2, c3⟩ := capelli (Module.End ℂ (S4 F)) (O.X D τ) (O.DX D τ) (O.dE D τ)
    (O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1)
    (O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1) (O.h (pl F τ))
    hXX hDD hDX (fun _ _ => rfl) rfl rfl hh
  generalize O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1 = q at he c1 c3
  generalize O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1 = Δ at hfo c1 c3
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have hk : cc * -cc⁻¹ = -1 := by
    rw [mul_neg, mul_inv_cancel₀ hcc]
  have k' : -cc⁻¹ * cc = -1 := by
    rw [neg_mul, inv_mul_cancel₀ hcc]
  have hef : O.e D.δ (pl F τ) * O.f D.δ (pl F τ) = -(q * Δ) := by
    rw [he, hfo, smul_mul_smul_comm, hk, neg_smul, one_smul]
  have hfe : O.f D.δ (pl F τ) * O.e D.δ (pl F τ) = -(Δ * q) := by
    rw [he, hfo, smul_mul_smul_comm, k', neg_smul, one_smul]
  have hP : Formalism.REAL.GlRel (Eop (a := 2) τ) := by
    intro i j k l
    have h := congrArg (Cm.uC E 2) (Cm.glRel_genC (a := 2) τ i j k l)
    simpa only [map_sub, map_mul, Cm.uC_genC, apply_ite (Cm.uC E 2), map_zero] using h
  have hst : ∀ i j, ∀ v ∈ π.V, TR.Eop (pl F τ) i j v ∈ π.V := fun i j v hv =>
    π.stable (.lie _) v hv
  have hfock := fun s hs => fockOps F E D O s hs
  have hme : ∀ v ∈ π.V, ∀ s ∈ Fock D.δ, Λ v (O.e D.δ (pl F τ) s) = -Λ (TR.Eop (pl F τ) 0 1 v) s := by
    intro v hv s hs
    refine Subtype.ext (funext fun g => ?_)
    change (Λ v (O.e D.δ (pl F τ) s)).1 g = -(Λ (TR.Eop (pl F τ) 0 1 v) s).1 g
    rw [hΛ v hv _ ((hfock s hs).2.2.1 _), hΛ _ (hst 0 1 v hv) s hs]
    exact hE v hv s hs _ g
  have hmf : ∀ v ∈ π.V, ∀ s ∈ Fock D.δ, Λ v (O.f D.δ (pl F τ) s) = -Λ (TR.Eop (pl F τ) 1 0 v) s := by
    intro v hv s hs
    refine Subtype.ext (funext fun g => ?_)
    change (Λ v (O.f D.δ (pl F τ) s)).1 g = -(Λ (TR.Eop (pl F τ) 1 0 v) s).1 g
    rw [hΛ v hv _ ((hfock s hs).2.2.2.1 _), hΛ _ (hst 1 0 v hv) s hs]
    exact moveF F E D W M π O hE v hv s hs _ g
  have h1 : O.e D.δ (pl F τ) * O.f D.δ (pl F τ) - O.f D.δ (pl F τ) * O.e D.δ (pl F τ) = O.h (pl F τ) := by
    rw [hef, hfe, ← c1]
    abel
  have h3 : (O.dE D τ 0 0 - O.dE D τ 1 1) * (O.dE D τ 0 0 - O.dE D τ 1 1) +
      2 * (O.dE D τ 0 1 * O.dE D τ 1 0 + O.dE D τ 1 0 * O.dE D τ 0 1) =
      O.h (pl F τ) * O.h (pl F τ) + 2 * (O.e D.δ (pl F τ) * O.f D.δ (pl F τ) + O.f D.δ (pl F τ) * O.e D.δ (pl F τ)) := by
    rw [c3, hef, hfe]
    noncomm_ring
  exact capAbs (TR.Sm F 2) (S4 F) (Sm E 2) π.V (Fock D.δ) Λ (TR.Eop (pl F τ)) (Eop τ) (O.dE D τ)
    (O.e D.δ (pl F τ)) (O.f D.δ (pl F τ)) (O.h (pl F τ)) (TR.glRel_Eop _) hP hst
    (fun i j s hs => (hfock s hs).2.2.2.2.2.1 τ i j) (fun s hs => (hfock s hs).2.2.1 _)
    (fun s hs => (hfock s hs).2.2.2.1 _)
    (fun i j v hv s hs => eopLift F E D W M π O Λ hΛ hL τ i j v hv s hs) hme hmf h1 c2 h3
    (u + ((2 : ℕ) - 1) / 2) f hf φ hφ
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LamEx

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.lamEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∃ Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ := by
  intro F E _ _ _ _ _ _ _ D W M π
  have hs := UpperTheory.ConvolutionTheory.R2.smooth F E D W M π
  have hl := UpperTheory.ConvolutionTheory.R2.Fo.liftLin F E D W M π
  let G : π.V → Fock D.δ → Sm E 2 := fun f φ => (hs f.1 f.2 φ.1 φ.2).choose
  have hG : ∀ f φ, (G f φ).1 = lift W M f.1.1 φ.1 := fun f φ => (hs f.1 f.2 φ.1 φ.2).choose_spec
  let L : π.V →ₗ[ℂ] Fock D.δ →ₗ[ℂ] Sm E 2 := LinearMap.mk₂ ℂ G
    (fun f f' φ => Subtype.ext (by
      have h := (hl f.1 f.2 φ.1 φ.2).1 f'.1 f'.2
      rw [Submodule.coe_add, hG, hG, hG]
      exact h))
    (fun c f φ => Subtype.ext (by
      have h := ((hl f.1 f.2 φ.1 φ.2).2.2 c).1
      rw [Submodule.coe_smul, hG, hG]
      exact h))
    (fun f φ φ' => Subtype.ext (by
      have h := (hl f.1 f.2 φ.1 φ.2).2.1 φ'.1 φ'.2
      rw [Submodule.coe_add, hG, hG, hG]
      exact h))
    (fun c f φ => Subtype.ext (by
      have h := ((hl f.1 f.2 φ.1 φ.2).2.2 c).2
      rw [Submodule.coe_smul, hG, hG]
      exact h))
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective π.V.subtype (Submodule.ker_subtype _)
  obtain ⟨s, hs'⟩ := LinearMap.exists_leftInverse_of_injective (Fock D.δ).subtype (Submodule.ker_subtype _)
  refine ⟨L.compl₁₂ r s, fun f hf φ hφ => ?_⟩
  have e1 : r f = ⟨f, hf⟩ := LinearMap.congr_fun hr ⟨f, hf⟩
  have e2 : s φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hs' ⟨φ, hφ⟩
  rw [LinearMap.compl₁₂_apply, e1, e2]
  exact hG _ _
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapOf

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), (∀ O, LieLift O W M π) → (∀ O, MoveE O W M π) → St.Cap W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h1 h2 τ m hm u Φ hΦ
  obtain ⟨O⟩ := opsEx F
  obtain ⟨Λ, hΛ⟩ := lamEx F E D W M π
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    obtain rfl : Φ = Λ f φ := Subtype.ext (e.trans (hΛ f hf φ hφ).symm)
    rw [capLam F E D W M π O Λ hΛ (h1 O) (h2 O) τ u f hf φ hφ]
    have := hm.2 u f hf
    rw [show pl F τ = InfinitePlace.mk (τ.comp (algebraMap F E)) from rfl, this, map_smul, LinearMap.smul_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]
end
end
