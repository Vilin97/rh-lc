module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAdjoinOfMulEqOne
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspli
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCo

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDual

section

@[expose] public section

namespace GlobalTheory.UnitLemma.TwistUnitAny

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem stable_of_unimodular (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (β x : B.A) (hβ : B.σ β = β * (ε * B.g)) (hx : B.σ x = x) (L : Submodule K.O B.A)
    (hU : ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm (β * x) y z ∈ (algebraMap K.O K.E).range) :
    ∀ y ∈ L, B.g * y ∈ L := by
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hsym : ∀ a b : B.A, T (β * x * a * B.σ b) ∈ R ↔ T (β * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← TwistUnit.trace_σ_mem B (β * x * a * B.σ b),
      show B.σ (β * x * a * B.σ b) = ε * (β * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  simp only [InvAlg.herm, ← hT, ← hR] at hU
  have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
    intro y hy
    rw [hU]
    intro y' hy'
    rw [hsym, show β * x * (B.g * (B.σ B.g * y)) * B.σ y' = β * x * y * B.σ y' by
      linear_combination (β * x * y * B.σ y') * hg]
    exact (hU y').1 hy' y hy
  intro y hy
  rw [hU]
  intro y' hy'
  have hb : B.σ B.g * (B.σ B.g * y') ∈ L := h1 _ (h1 y' hy')
  have := (hU _).1 hb y hy
  rw [hsym] at this
  rw [show β * x * y' * B.σ (B.g * y) = β * x * (B.g * (B.σ B.g * (B.σ B.g * y'))) * B.σ y by
    rw [map_mul]; linear_combination (-(β * x * y' * B.σ B.g * B.σ y)) * hg]
  exact this

theorem twisted_unit_eq_unit_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable →
    ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs ε hε
  by_cases hi : IsIntegral K.O B.g
  · exact TwistUnit.twisted_unit_eq_unit K B hg hs hi ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hu : (ε * B.g) * B.σ (ε * B.g) = 1 := by
    rw [map_mul, hσε]; linear_combination B.g * B.σ B.g * hεε + hg
  obtain ⟨β₀, hβ⟩ := GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma K B (ε * B.g) hu
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hLat, hU⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g
      (stable_of_unimodular B hg ε hε β₀ x hβ hx L hU)) hi
  · rintro ⟨hLat, h2, -⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g h2) hi

end GlobalTheory.UnitLemma.TwistUnitAny
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDualStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ ∀ x : B.Aˣ, B.σ (x : B.A) = x → {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  first | exact @GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | exact GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | (intros; apply GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPoly

section

@[expose] public section

open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable section

namespace InertUnit

variable {K : UQ} {P : K.E[X]}

theorem coeff_mul (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    K.c (P.coeff 0) * P.coeff 0 = 1 := by
  have h := congrArg (fun Q => Q.coeff 0) hr
  simp only [coeff_C_mul, coeff_zero_reverse] at h
  rw [h, leadingCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff]), hP.leadingCoeff, map_one]

def rootInv (P : K.E[X]) : AdjoinRoot P :=
  -(algebraMap K.E (AdjoinRoot P) (K.c (P.coeff 0))) * aeval (AdjoinRoot.root P) P.divX

theorem root_mul_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot.root P * rootInv P = 1 := by
  have h0 : aeval (AdjoinRoot.root P) P = 0 := AdjoinRoot.aeval_eq P ▸ AdjoinRoot.mk_self
  have h1 := congrArg (aeval (AdjoinRoot.root P)) (X_mul_divX_add P)
  rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at h1
  have h2 : AdjoinRoot.root P * aeval (AdjoinRoot.root P) P.divX = -algebraMap K.E (AdjoinRoot P) (P.coeff 0) :=
    eq_neg_of_add_eq_zero_left h1
  unfold rootInv
  rw [mul_left_comm, h2, neg_mul_neg, ← map_mul, coeff_mul hP hr, map_one]

theorem eval_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    P.eval₂ ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) = 0 := by
  have hu := root_mul_rootInv hP hr
  letI : Invertible (rootInv P) := ⟨AdjoinRoot.root P, hu, by rw [mul_comm]; exact hu⟩
  rw [← eval₂_map, ← eval₂_reverse_mul_pow]
  have : ⅟(rootInv P) = AdjoinRoot.root P := rfl
  rw [this, ← hr, eval₂_mul, eval₂_C]
  have h0 : P.eval₂ (algebraMap K.E (AdjoinRoot P)) (AdjoinRoot.root P) = 0 := AdjoinRoot.eval₂_root P
  rw [h0, mul_zero, zero_mul]

def sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot P →+* AdjoinRoot P :=
  AdjoinRoot.lift ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) (eval_rootInv hP hr)

theorem sig_alg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) (e : K.E) :
    sig hP hr (algebraMap K.E (AdjoinRoot P) e) = algebraMap K.E (AdjoinRoot P) (K.c e) := by
  rw [AdjoinRoot.algebraMap_eq, sig, AdjoinRoot.lift_of]
  rfl

theorem sig_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    sig hP hr (AdjoinRoot.root P) = rootInv P := AdjoinRoot.lift_root _

theorem sig_sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (sig hP hr).comp (sig hP hr) = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← AdjoinRoot.algebraMap_eq, sig_alg, sig_alg, K.c_c]
  · simp only [RingHom.comp_apply, RingHom.id_apply, sig_root]
    have hu := root_mul_rootInv hP hr
    have h1 : sig hP hr (AdjoinRoot.root P) * sig hP hr (rootInv P) = 1 := by rw [← map_mul, hu, map_one]
    rw [sig_root] at h1
    calc sig hP hr (rootInv P) = (AdjoinRoot.root P * rootInv P) * sig hP hr (rootInv P) := by rw [hu, one_mul]
      _ = AdjoinRoot.root P * (rootInv P * sig hP hr (rootInv P)) := by ring
      _ = AdjoinRoot.root P := by rw [h1, mul_one]

def invAlg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) : InvAlg K where
  A := AdjoinRoot P
  fd := (AdjoinRoot.powerBasis hP.ne_zero).finite
  σ := RingEquiv.ofRingHom (sig hP hr) (sig hP hr) (sig_sig hP hr) (sig_sig hP hr)
  σ_σ := fun y => congrArg (fun f : AdjoinRoot P →+* AdjoinRoot P => f y) (sig_sig hP hr)
  σ_alg := sig_alg hP hr
  g := AdjoinRoot.root P

theorem charpoly_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (invAlg hP hr).P = P := by
  haveI : Module.Finite K.E (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
    AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
  exact h

end InertUnit

open InertUnit in
theorem exists_invAlg_root : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic →
    C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse →
    ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  intro K P hP hr
  refine ⟨invAlg hP hr, ?_, charpoly_root hP hr⟩
  show AdjoinRoot.root P * sig hP hr (AdjoinRoot.root P) = 1
  rw [sig_root]
  exact root_mul_rootInv hP hr
end
end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPolyStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic → C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  first | exact @GlobalTheory.UnitLemma.exists_invAlg_root | exact GlobalTheory.UnitLemma.exists_invAlg_root | (intros; apply GlobalTheory.UnitLemma.exists_invAlg_root <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspliStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  first | exact @GlobalTheory.TwClassForms.twCl_equiv_cl | exact GlobalTheory.TwClassForms.twCl_equiv_cl | (intros; apply GlobalTheory.TwClassForms.twCl_equiv_cl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) δ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | exact GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | (intros; apply GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertTwUnit

theorem cast_finsum_rat {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h1 : (Function.support f).Infinite := h
    have h2 : (Function.support fun i => (f i : ℂ)).Infinite := by
      have e : (Function.support fun i => (f i : ℂ)) = Function.support f := by
        ext i; simp
      rw [e]; exact h1
    rw [finsum_of_infinite_support h1, finsum_of_infinite_support h2, Rat.cast_zero]

theorem twisted_unit_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  intro E _ _ _ hU w hw K e hc hr hv hq a Q hm hd hs hQ
  unfold stTw IsCsr at *
  unfold clSum
  have hQ' : C ((cj w) (Q.coeff 0)) * Q = (Q.map (cj w)).reverse := hQ.resolve_left hw
  have hcomm : e.symm.toRingHom.comp (cj w) = (K.c : K.E →+* K.E).comp e.symm.toRingHom := by
    ext y
    have h := congrArg e.symm (hc (e.symm y))
    simp only [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h
    simp [h]
  have hrev : ∀ p : (w.adicCompletion E)[X],
      (p.reverse).map e.symm.toRingHom = (p.map e.symm.toRingHom).reverse := by
    intro p
    unfold Polynomial.reverse
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective, Polynomial.reflect_map]
  have hPr : C (K.c ((Q.map e.symm.toRingHom).coeff 0)) * Q.map e.symm.toRingHom =
      ((Q.map e.symm.toRingHom).map (K.c : K.E →+* K.E)).reverse := by
    have h1 := congrArg (Polynomial.map e.symm.toRingHom) hQ'
    have h0 : e.symm.toRingHom ((cj w) (Q.coeff 0)) = K.c ((Q.map e.symm.toRingHom).coeff 0) := by
      rw [Polynomial.coeff_map]
      exact RingHom.congr_fun hcomm (Q.coeff 0)
    rw [Polynomial.map_mul, Polynomial.map_C, h0] at h1
    rw [h1, hrev, Polynomial.map_map, hcomm, ← Polynomial.map_map]
  obtain ⟨B, hg, hP⟩ := GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly K (Q.map e.symm.toRingHom) (hm.map _) hPr
  have hsep : B.P.Separable := by
    rw [hP]
    exact hs.map
  refine ⟨B, hg, hP, ?_⟩
  have hε : (-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1 := neg_one_pow_eq_or B.A (a - 1)
  obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual K B hg hsep _ hε
  obtain ⟨F, hF⟩ := GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit E hU w hw K e hc hr a Q hm hd hs B hg hP β₀ hβ₀
  have hterm : ∀ k : B.Cl, twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (F k).1.rep
      ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((B.N k.rep : ℚ) : ℂ) := by
    intro k
    obtain ⟨b, hb⟩ := hF k
    have hu : B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = ((Quot.out k).1 : B.Aˣ) := (Quot.out k).2
    have hβ : B.σ ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) =
        (β₀ * (Quot.out k).1 : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
      rw [Units.val_mul, map_mul, hβ₀, hu]
      ring
    have h := GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount E hU w hw K e hc hr a B hsep (β₀ * (Quot.out k).1) _ hε hβ b (F k).1.rep
      (fun i j => by rw [Units.val_mul]; exact hb i j)
    rw [h, Units.val_mul, hX _ hu]
    rfl
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul]
  simp only [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv F]
  simp only [hterm]
  exact (cast_finsum_rat _).symm

end GlobalTheory.InertTwUnit
end
end
end
