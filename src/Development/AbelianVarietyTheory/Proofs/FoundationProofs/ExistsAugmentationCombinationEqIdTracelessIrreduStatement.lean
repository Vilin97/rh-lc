module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThreeStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZeroStatement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducibleStatement
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZero

section

@[expose] public section

open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem one_mem_of_mulClosed_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)),
    (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  intro F K _ _ _ _ m S hS T hT hdet
  classical
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet)
  have hint : IsIntegral F T := by
    have hK : IsIntegral K T := Algebra.IsIntegral.isIntegral T
    exact isIntegral_trans T hK
  have hpow : ∀ n : ℕ, T ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ]; exact hS _ ih _ hT
  have hmul : ∀ q : F[X], T * aeval T q ∈ S := by
    intro q
    rw [aeval_eq_sum_range, Finset.mul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']
    exact S.smul_mem _ (hpow i)
  set p := minpoly F T with hpdef
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hkey : T * aeval T p.divX + algebraMap F _ (p.coeff 0) = 0 := by
    have h0 : aeval T p = 0 := minpoly.aeval F T
    have e : aeval T p = T * aeval T p.divX + algebraMap F _ (p.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add p, mul_comm p.divX X]
      simp only [map_add (f := _), map_mul, aeval_X, aeval_C]
    rw [← e, h0]
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero, add_zero] at hkey
    have hq : aeval T p.divX = 0 := by
      exact hTu.mul_right_eq_zero.1 hkey
    have hne : p.divX ≠ 0 := by
      intro h
      rw [divX_eq_zero_iff, hc, map_zero] at h
      exact hp0 h
    have hle := minpoly.degree_le_of_ne_zero F T hne hq
    exact absurd (degree_divX_lt hp0) (not_lt.2 hle)
  have hone : (1 : Matrix (Fin m) (Fin m) K) = (-(p.coeff 0)⁻¹) • (T * aeval T p.divX) := by
    rw [eq_neg_of_add_eq_zero_left hkey, smul_neg, neg_smul, neg_neg, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hc, map_one]
  rw [hone]
  exact S.smul_mem _ (hmul _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZeroStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)), (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | exact GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | (intros; apply GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducible

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory

theorem ad_invariant_eq_zero_of_isIrr {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ]
    (ρ : Γ →* GL (Fin 2) K) (hρ : IsIrr ρ) (v : Fin 3 → K) (hv : ∀ g, ad (ρ g) *ᵥ v = v) : v = 0 := by
  set Y : Matrix (Fin 2) (Fin 2) K := ofCoord v with hY

  have hcomm : ∀ g, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
    intro g
    have h1 : coord ((ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = coord Y := by
      rw [coord_conj_ofCoord, hv g, coord_ofCoord]
    have h2 : (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y := by
      have := congrArg ofCoord h1
      rwa [ofCoord_coord (by rw [trace_conj, trace_ofCoord]), ofCoord_coord (trace_ofCoord v)] at this
    calc (ρ g : Matrix (Fin 2) (Fin 2) K) * Y
        = (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc _ _ (ρ g : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hW
  have hWne : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
  have hWinv : IsInv ρ W := by
    intro g x hx
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have hWtop : W = ⊤ := by
    rcases hρ.2.2 W le_top hWinv with h | h
    · exact absurd h hWne
    · exact h
  have hYμ : Y = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    have hx : (Pi.single j 1 : Fin 2 → K) ∈ W := by rw [hWtop]; trivial
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_single_one] at hx
    have := congrFun hx i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  have htr : (2 : K) * μ = 0 := by
    have := trace_ofCoord v
    rw [← hY, hYμ, Matrix.trace_smul, Matrix.trace_one] at this
    simpa [mul_comm] using this
  have hμ0 : μ = 0 := by
    rcases mul_eq_zero.mp htr with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hY0 : Y = 0 := by rw [hYμ, hμ0, zero_smul]
  rw [← coord_ofCoord v, ← hY, hY0]
  ext i; fin_cases i <;> simp [coord]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducibleStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

theorem _root_.GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ v : Fin 3 → K, (∀ g, ad (ρ g) *ᵥ v = v) → v = 0 := by
  first | exact @GlobalTheory.ad_invariant_eq_zero_of_isIrr | exact GlobalTheory.ad_invariant_eq_zero_of_isIrr | (intros; apply GlobalTheory.ad_invariant_eq_zero_of_isIrr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrredu

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Sl2Ad

theorem form_isSymm {K : Type} [Field K] : (form (K := K)).IsSymm := by
  first
  | exact ⟨fun v w => by simp only [RingHom.id_apply, form_apply]; ring⟩
  | exact fun v w => by simp only [RingHom.id_apply, form_apply]; ring
  | (intro v w; simp only [RingHom.id_apply, form_apply]; ring)

theorem form_ad {K : Type} [Field K] (A : GL (Fin 2) K) (v w : Fin 3 → K) :
    form (ad A *ᵥ v) (ad A *ᵥ w) = form v w := by
  rw [← coord_conj_ofCoord, ← coord_conj_ofCoord,
    form_coord (by rw [trace_conj, trace_ofCoord]) (by rw [trace_conj, trace_ofCoord])]
  conv_rhs => rw [← coord_ofCoord v, ← coord_ofCoord w, form_coord (trace_ofCoord v) (trace_ofCoord w)]
  have : ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord w * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = (A : Matrix (Fin 2) (Fin 2) K) * (ofCoord v * ofCoord w) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), h, Matrix.one_mul]
  rw [this, trace_conj]

theorem form_nondegenerate {K : Type} [Field K] [CharZero K] : (form (K := K)).Nondegenerate := by
  rw [form, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  simp [Matrix.det_fin_three]

theorem coord_smul_scalar {F K : Type} [Field F] [Field K] [Algebra F K] (a : F) (X : Matrix (Fin 2) (Fin 2) K) :
    coord (a • X) = a • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_sum {K : Type} [Field K] {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) K) :
    coord (∑ i ∈ s, f i) = ∑ i ∈ s, coord (f i) := by
  ext j; fin_cases j <;> simp [coord, Matrix.sum_apply]

end GlobalTheory.Sl2Ad


open GlobalTheory.Sl2Ad in
theorem GlobalTheory.Sl2Ad.augmentation_contains_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  intro l _ c Γ _ r _ hirr
  set S : Γ →* Matrix (Fin 3) (Fin 3) (Qbar l) := adHom.comp r with hS
  have hSg : ∀ g, S g = ad (r g) := fun g => rfl
  have h1 := GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three S form form_nondegenerate form_isSymm (fun g v w => form_ad _ v w)
    (fun v hv => GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr r hirr v (fun g => by rw [← hSg]; exact hv g))
    (fun y hy hy' => GlobalTheory.T.traceForm_ne_zero_of_stable_line_irreducible r hirr y hy (fun g => by rw [← hSg]; exact hy' g))
  obtain ⟨n, b, g, hg⟩ := Submodule.mem_span_set'.mp h1
  choose γ hγ using fun i => (g i).2
  have hdet : (∑ i, b i • (S (γ i) - 1)).det ≠ 0 := by
    have : ∑ i, b i • (S (γ i) - 1) = 1 :=
      (Finset.sum_congr rfl fun i _ => by rw [← hγ i]).trans hg
    rw [this, Matrix.det_one]; exact one_ne_zero
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_nat_coeffs_det_sum_smul_ne_zero (fun i => S (γ i) - 1) b hdet
  set J : Submodule ℚ_[l] (Matrix (Fin 3) (Fin 3) (Qbar l)) := Submodule.span ℚ_[l] (Set.range fun g => S g - 1) with hJ
  have hmul : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        have : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
          rw [map_mul]; noncomm_ring
        rw [this]
        exact J.sub_mem (J.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
      | zero => rw [mul_zero]; exact J.zero_mem
      | add y z _ _ hy hz => rw [mul_add]; exact J.add_mem hy hz
      | smul t y _ hy => rw [mul_smul_comm]; exact J.smul_mem t hy
    | zero => rw [zero_mul]; exact J.zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact J.add_mem hx hz
    | smul t x _ hx => rw [smul_mul_assoc]; exact J.smul_mem t hx
  have hT : (∑ i, (a i : Qbar l) • (S (γ i) - 1)) ∈ J := by
    refine J.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact J.nsmul_mem (Submodule.subset_span ⟨_, rfl⟩) _
  have hone := GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero J hmul _ hT ha
  obtain ⟨n', a', g', hg'⟩ := Submodule.mem_span_set'.mp hone
  choose γ' hγ' using fun i => (g' i).2
  refine ⟨n', γ', a', fun X hX => ?_⟩
  have htr : (∑ i, a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) - X)).trace = 0 := by
    rw [Matrix.trace_sum]; refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_sub, trace_conj, hX, sub_zero, smul_zero]
  refine ((ofCoord_coord hX).symm.trans ?_).trans (ofCoord_coord htr)
  congr 1
  rw [coord_sum]
  have : ∀ i, coord (a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X))
      = (a' i • (S (γ' i) - 1)) *ᵥ coord X := by
    intro i
    rw [coord_smul_scalar, show ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X)
      = (r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) + (-1 : Qbar l) • X by
        rw [neg_one_smul, ← sub_eq_add_neg], coord_add, coord_conj _ hX, coord_smul, hSg, Matrix.smul_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, neg_one_smul, ← sub_eq_add_neg]
  simp_rw [this, ← Matrix.sum_mulVec]
  have e : ∑ i, a' i • (S (γ' i) - 1) = 1 :=
    (Finset.sum_congr rfl fun i _ => by rw [← hγ' i]).trans hg'
  rw [e, Matrix.one_mulVec]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrreduStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_augmentation_combination_eq_id_traceless_irreducible : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  first | exact @GlobalTheory.Sl2Ad.augmentation_contains_one | exact GlobalTheory.Sl2Ad.augmentation_contains_one | (intros; apply GlobalTheory.Sl2Ad.augmentation_contains_one <;> assumption)
end
end
