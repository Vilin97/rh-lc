module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpolyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfEqualGramTraceForms

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitLemma.IsometryUnit

theorem isometry_unit : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  intro K B hs ε hε a β β' hβ hβ' b b' hgram
  have hs' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hs
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y; rw [Algebra.smul_def, map_mul, B.σ_alg, Algebra.smul_def]
  have trσ := GlobalTheory.UnitLemma.PairClass.trace_σ K B
  have addL : ∀ (x u u' v : B.A), B.herm x (u + u') v = B.herm x u v + B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)]
  have subL : ∀ (x u u' v : B.A), B.herm x (u - u') v = B.herm x u v - B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]
  have smulL : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x (r • u) v = r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have addR : ∀ (x u v v' : B.A), B.herm x u (v + v') = B.herm x u v + B.herm x u v' := by
    intro x u v v'; unfold InvAlg.herm; rw [map_add (f := _), mul_add, map_add (f := _)]
  have smulR : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x u (r • v) = K.c r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [σsm, mul_smul_comm, map_smul, smul_eq_mul]

  have asym : ∀ (x : B.A), B.σ x = x * (ε * B.g) → ∀ z y, K.c (B.herm x z y) = B.herm x (ε * B.g * y) z := by
    intro x hx z y; unfold InvAlg.herm
    rw [← trσ]; congr 1; simp only [map_mul, B.σ_σ, hx]; ring

  have nd : ∀ x : B.A, (∀ y, Algebra.trace K.E B.A (x * y) = 0) → x = 0 :=
    fun x hx => GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hs' x hx
  have ndh : ∀ w : B.A, (∀ z, B.herm β w z = 0) → w = 0 := by
    intro w hw
    have h0 : (β : B.A) * w = 0 := nd _ (fun y => by
      have := hw (B.σ y); unfold InvAlg.herm at this; rwa [B.σ_σ] at this)
    have := congrArg (fun z => ((β⁻¹ : B.Aˣ) : B.A) * z) h0
    simpa [← mul_assoc] using this

  let φ : B.A ≃ₗ[K.E] B.A := b'.equiv b (Equiv.refl _)
  have hφb : ∀ i, φ (b' i) = b i := fun i => by simp [φ, Module.Basis.equiv_apply]
  have hφ : ∀ u v, B.herm β (φ u) (φ v) = B.herm β' u v := by
    let F₁ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β (φ u) (φ v))
        (fun u u' v => by rw [map_add (f := _), addL]) (fun r u v => by rw [map_smul, smulL]; rfl)
        (fun u v v' => by rw [map_add (f := _), addR]) (fun r u v => by rw [map_smul, smulR]; rfl)
    let F₂ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β' u v)
        (fun u u' v => addL _ _ _ _) (fun r u v => smulL _ _ _ _)
        (fun u v v' => addR _ _ _ _) (fun r u v => smulR _ _ _ _)
    have hF : F₁ = F₂ := LinearMap.ext_basis b' b' (fun i j => by
      simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply, hφb]; exact hgram i j)
    intro u v
    have := LinearMap.congr_fun₂ hF u v
    simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply] at this
    exact this
  have hcomm : ∀ u, φ (ε * B.g * u) = ε * B.g * φ u := by
    intro u
    rw [← sub_eq_zero]
    apply ndh
    intro z
    obtain ⟨v, rfl⟩ : ∃ v, φ v = z := ⟨φ.symm z, by simp⟩
    rw [subL, hφ, ← asym _ hβ', ← hφ, asym _ hβ, sub_self]
  have hg : ∀ u, φ (B.g * u) = B.g * φ u := by
    intro u
    rcases hε with rfl | rfl
    · simpa using hcomm u
    · have := hcomm u
      simp only [neg_mul, one_mul, map_neg, neg_inj] at this
      exact this
  have hpoly : ∀ q : K.E[X], ∀ u, φ (aeval B.g q * u) = aeval B.g q * φ u := by
    intro q
    induction q using Polynomial.induction_on with
    | C r => intro u; rw [aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add p q hp hq => intro u; rw [map_add (f := _), add_mul, add_mul, map_add (f := _), hp, hq]
    | monomial n r h =>
      intro u
      have e : aeval B.g (C r * X ^ (n + 1)) = aeval B.g (C r * X ^ n) * B.g := by
        simp [pow_succ, mul_assoc]
      rw [e, mul_assoc, h, hg, mul_assoc]
  have hmul : ∀ y, φ y = y * φ 1 := by
    intro y
    obtain ⟨q, rfl⟩ := GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable B.g hs' y
    simpa using hpoly q 1
  have ht : IsUnit (φ 1) := by
    have := hmul (φ.symm 1)
    rw [LinearEquiv.apply_symm_apply] at this
    exact ⟨⟨φ 1, φ.symm 1, by rw [mul_comm]; exact this.symm, this.symm⟩, rfl⟩
  refine ⟨ht.unit, ?_⟩
  rw [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply nd
  intro y
  have h1 := hφ y 1
  rw [hmul y] at h1
  unfold InvAlg.herm at h1
  rw [map_one B.σ, mul_one] at h1
  have h2 : ((β' : B.A) - β * (φ 1 * B.σ (φ 1))) * y = (β' : B.A) * y - β * (y * φ 1) * B.σ (φ 1) := by ring
  rw [h2, map_sub, h1, sub_self]

end GlobalTheory.UnitLemma.IsometryUnit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfEqualGramTraceFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_norm_of_equal_gram_traceForms : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  first | exact @GlobalTheory.UnitLemma.IsometryUnit.isometry_unit | exact GlobalTheory.UnitLemma.IsometryUnit.isometry_unit | (intros; apply GlobalTheory.UnitLemma.IsometryUnit.isometry_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChangeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.gramMatrix_traceForm_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  first | exact @GlobalTheory.GramChange.gram_basis_change | exact GlobalTheory.GramChange.gram_basis_change | (intros; apply GlobalTheory.GramChange.gram_basis_change <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwistStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.hermitian_form_det_unit_and_twist : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  first | exact @GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | exact GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | (intros; apply GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspli

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwClassForms

theorem twConj_gram (L : Type) [Field L] (c : L →+* L) (a : ℕ) (δ q : GL (Fin a) L) :
    (((q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ =
      q.valᵀ * ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * q.val.map c := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hinv : (GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ := Matrix.inv_eq_left_inv hΦ'
  have hθ : (thetaGL a c q).val =
      GlobalTheory.Tw.Phi a L * ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  have hC : ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (q.val.map c)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, show q.val.map c = (GeneralLinearGroup.map c q).val from rfl,
      Units.mul_inv, Matrix.transpose_one]
  have k1 : ∀ X : Matrix (Fin a) (Fin a) L, (GlobalTheory.Tw.Phi a L)ᵀ * (GlobalTheory.Tw.Phi a L * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ', Matrix.one_mul]
  have k2 : ∀ X : Matrix (Fin a) (Fin a) L, ((GeneralLinearGroup.map c q)⁻¹).valᵀ * ((q.val.map c)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have k3 : ∀ X : Matrix (Fin a) (Fin a) L, GlobalTheory.Tw.Phi a L * ((GlobalTheory.Tw.Phi a L)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul]
  have k4 : ∀ X : Matrix (Fin a) (Fin a) L, δ.val * ((δ⁻¹).val * X) = X := by
    intro X; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hY : (q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L *
      ((q.val.map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹).val * q.val) = 1 := by
    simp only [Units.val_mul, hθ, Matrix.mul_assoc, k1, k2, k3, k4]
    exact Units.inv_mul q
  rw [Matrix.inv_eq_right_inv hY, Matrix.mul_inv_rev, hinv, ← Matrix.coe_units_inv]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem gram_delta (L : Type) [Field L] (a : ℕ) :
    (∀ G : Matrix (Fin a) (Fin a) L, IsUnit G.det → ∃ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G) ∧
    (∀ δ δ' : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ'.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ → δ = δ') := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hdΦ : IsUnit (GlobalTheory.Tw.Phi a L).det := Matrix.isUnit_det_of_right_inverse hΦ
  refine ⟨fun G hG => ?_, fun δ δ' h => ?_⟩
  · have hGT : IsUnit (Gᵀ)⁻¹.det := by
      rw [Matrix.det_nonsing_inv, Matrix.det_transpose]; exact hG.ringInverse
    have hd : IsUnit ((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]; exact hGT.mul hdΦ
    refine ⟨Matrix.nonsingInvUnit _ hd, ?_⟩
    change (((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G
    rw [Matrix.mul_assoc, hΦ', Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hG),
      Matrix.transpose_transpose]
  · have hu : ∀ x : GL (Fin a) L, IsUnit (x.val * GlobalTheory.Tw.Phi a L).det := by
      intro x; rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units x).mul hdΦ
    have h1 := congrArg Matrix.transpose h
    simp only [Matrix.transpose_transpose] at h1
    have h2 := congrArg Inv.inv h1
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu δ), Matrix.nonsing_inv_nonsing_inv _ (hu δ')] at h2
    have h3 := congrArg (· * (GlobalTheory.Tw.Phi a L)ᵀ) h2
    simp only [Matrix.mul_assoc, hΦ, Matrix.mul_one] at h3
    exact Units.ext h3

theorem herm_norm_basis (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (a : ℕ) (β t : B.Aˣ)
    (b : Module.Basis (Fin a) K.E B.A) : ∃ b' : Module.Basis (Fin a) K.E B.A,
      ∀ i j, B.herm ((β : B.A) * (t * B.σ t)) (b i) (b j) = B.herm β (b' i) (b' j) := by
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (t : B.A))
    (LinearMap.mulLeft K.E ((t⁻¹ : B.Aˣ) : B.A))
    (by ext y; simp [← mul_assoc]) (by ext y; simp [← mul_assoc])
  refine ⟨b.map f, fun i j => ?_⟩
  simp only [Module.Basis.map_apply, f, LinearEquiv.ofLinear_apply, LinearMap.mulLeft_apply,
    GlobalTheory.UnitLemma.InvAlg.herm, map_mul]
  congr 1
  ring

theorem twCl_equiv_cl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  intro E _ _ _ hE w hw K e he hO a Q hQm hQd hQs B hg hP β₀ hβ₀
  have hthL : thL a w = thetaGL a (cj w) := by rw [thL, if_neg hw]
  have hnrm : ∀ y, nrmL a w y = y * thetaGL a (cj w) y := by intro y; rw [nrmL, if_neg hw]
  have hcc : ∀ x, cj w (cj w x) = x := by
    intro x; obtain ⟨y, rfl⟩ := e.surjective x; rw [← he, ← he, K.c_c]
  have hPsep : B.P.Separable := by rw [hP]; exact hQs.map
  have hfr : Module.finrank K.E B.A = a := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E B.g)]
    change B.P.natDegree = a
    rw [hP, natDegree_map, hQd]
  let b0 : Module.Basis (Fin a) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hfr
  have hε : ((-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1) := neg_one_pow_eq_or B.A (a - 1)
  have hβx : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
      B.σ ((β₀ * x : B.Aˣ) : B.A) = (β₀ * x : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
    intro x hx; simp only [Units.val_mul, map_mul, hβ₀, hx]; ring

  have htwE : ∀ δ δ' : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) δ δ' →
      ∃ q, δ' = q⁻¹ * δ * thL a w q := by
    intro δ δ' h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨q, rfl⟩ := ih
      exact ⟨q⁻¹, by simp [mul_assoc]⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨q, rfl⟩ := ih1
      obtain ⟨r, rfl⟩ := ih2
      exact ⟨q * r, by simp [mul_assoc]⟩
  have hσinv : ∀ u : B.Aˣ, B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) = 1 := by
    intro u; rw [← map_mul, Units.inv_mul, map_one]
  have hclE : ∀ x y : {x : B.Aˣ // B.σ (x : B.A) = x}, Relation.EqvGen (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) x y → ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A)) := by
    intro x y h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨u⁻¹, ?_⟩
      have h1 := hσinv u
      have h2 : ((u⁻¹ : B.Aˣ) : B.A) * u = 1 := Units.inv_mul u
      rw [hu]
      linear_combination (-(x.1 : B.A) * (B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A))) * h2 - (x.1 : B.A) * h1
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨u, hu⟩ := ih1
      obtain ⟨v, hv⟩ := ih2
      exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩

  obtain ⟨F0i, F0u⟩ := gram_delta (w.adicCompletion E) a
  have hF1 := GlobalTheory.T.hermitian_form_det_unit_and_twist K B (w.adicCompletion E) e (cj w) he hcc a Q hP hQs hQd
  have hF4 := GlobalTheory.T.gramMatrix_traceForm_basis_change K B (w.adicCompletion E) e (cj w) he a
  have hF6 := twConj_gram (w.adicCompletion E) (cj w) a
  have hcl : ∀ k : B.Cl, B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = (Quot.out k).1 := fun k => (Quot.out k).2
  have hG : ∀ k : B.Cl, IsUnit (Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b0 i) (b0 j))).det :=
    fun k => (hF1 _ (hβx _ (hcl k)) b0).1
  choose δk hδk using fun k => F0i _ (hG k)

  have hrep : ∀ k : B.Cl, ∀ δ : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) (δk k) δ →
      ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ =
        Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b i) (b j)) := by
    intro k δ h
    obtain ⟨q, rfl⟩ := htwE _ _ h
    rw [hthL, hF6, hδk k]
    obtain ⟨b', hb'⟩ := (hF4 _ b0).1 q
    exact ⟨b', hb'.symm⟩
  let F : B.Cl → {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q} := fun k =>
    ⟨Quot.mk _ (δk k), by
      obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k)))).symm
      rw [hnrm]
      exact (hF1 _ (hβx _ (hcl k)) b).2 _ hb⟩
  have hinj : Function.Injective F := by
    intro k k' hkk
    have h1 : (Quot.mk _ (δk k) : TwCl (thL a w)) = Quot.mk _ (δk k') := congrArg Subtype.val hkk
    obtain ⟨b', hb'⟩ := hrep k _ (Quot.eqvGen_exact h1)
    rw [hδk k'] at hb'
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_norm_of_equal_gram_traceForms K B hPsep _ hε a _ _ (hβx _ (hcl k')) (hβx _ (hcl k)) b0 b' (fun i j => by
      have := congrFun (congrFun hb' i) j
      simpa using e.injective this)
    have hrel : (Quot.mk _ (Quot.out k') : B.Cl) = Quot.mk _ (Quot.out k) := by
      apply Quot.sound
      refine ⟨t, ?_⟩
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul] at ht
      linear_combination ((β₀⁻¹ : B.Aˣ) : B.A) * ht - (((Quot.out k).1 : B.A) - ((Quot.out k').1 : B.A) * ((t : B.A) * B.σ (t : B.A))) * h2
    exact (Quot.out_eq k).symm.trans (hrel.symm.trans (Quot.out_eq k'))

  have hsurj : Function.Surjective F := by
    rintro ⟨cl, hclQ⟩
    have hQδ : ((Quot.out cl) * thetaGL a (cj w) (Quot.out cl)).val.charpoly = Q := by
      rw [← hnrm]; exact hclQ
    obtain ⟨β, hβ, b, hb⟩ := GlobalTheory.T.exists_traceForm_of_twistedNorm_charpoly K B (w.adicCompletion E) e (cj w) he hcc hg a Q hP hQs hQd _ hQδ
    have hx : B.σ (((β₀⁻¹ * β : B.Aˣ)) : B.A) = ((β₀⁻¹ * β : B.Aˣ) : B.A) := by
      have h1 : B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * ((β₀ : B.A) * ((-1) ^ (a - 1) * B.g)) = 1 := by
        rw [← hβ₀, ← map_mul, Units.inv_mul, map_one]
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul, map_mul, hβ]
      linear_combination (((β₀⁻¹ : B.Aˣ) : B.A) * β) * h1 - (B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * β * ((-1) ^ (a - 1) * B.g)) * h2
    let k : B.Cl := Quot.mk _ ⟨β₀⁻¹ * β, hx⟩
    refine ⟨k, ?_⟩
    obtain ⟨u, hu⟩ := hclE _ _ (Quot.eqvGen_exact (Quot.out_eq k)).symm
    have hβu : ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) = (β : B.A) * ((u : B.A) * B.σ (u : B.A)) := by
      rw [Units.val_mul, hu, Units.val_mul]
      have h2 : (β₀ : B.A) * ((β₀⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv β₀
      linear_combination ((β : B.A) * ((u : B.A) * B.σ (u : B.A))) * h2
    obtain ⟨b'', hb''⟩ := herm_norm_basis K B a β u b0
    obtain ⟨P, hPb⟩ := (hF4 (β : B.A) b).2 b''
    have hmat : ((δk k).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ =
        (((P⁻¹ * Quot.out cl * thetaGL a (cj w) P)).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ := by
      rw [hF6, hb, ← hPb, hδk k]
      ext i j
      simp only [Matrix.of_apply, hβu, hb'']
    have hδeq := F0u _ _ hmat
    apply Subtype.ext
    change (Quot.mk _ (δk k) : TwCl (thL a w)) = cl
    rw [hδeq]
    have hθP : thL a w P = thetaGL a (cj w) P := by rw [hthL]
    exact (Quot.sound (⟨P, by rw [hθP]⟩ : ∃ g, P⁻¹ * Quot.out cl * thetaGL a (cj w) P = g⁻¹ * Quot.out cl * thL a w g)).symm.trans (Quot.out_eq cl)
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k) : TwCl (thL a w)))).symm
  refine ⟨b, fun i j => ?_⟩
  have := congrFun (congrFun hb i) j
  rw [Matrix.of_apply, Units.val_mul] at this
  exact this

end GlobalTheory.TwClassForms
end
end
