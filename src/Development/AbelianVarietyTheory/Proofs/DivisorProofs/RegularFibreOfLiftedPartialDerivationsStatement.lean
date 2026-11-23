module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Derivation.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrimeStatement
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFibreOfJacobianDerivationsStatement
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendMvPolynomial

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory


open MvPolynomial in
noncomputable def coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) : MvPolynomial τ B :=
  ∑ s ∈ p.support, MvPolynomial.monomial s (D (p.coeff s))

open MvPolynomial in
theorem coeff_coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) (m : τ →₀ ℕ) :
    (coeffDerivFun D p).coeff m = D (p.coeff m) := by
  classical
  rw [coeffDerivFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

noncomputable def coeffDerivAddHom {B τ : Type} [CommRing B] (D : Derivation ℤ B B) :
    MvPolynomial τ B →+ MvPolynomial τ B where
  toFun := coeffDerivFun D
  map_zero' := by ext m; simp [coeff_coeffDerivFun]
  map_add' p q := by ext m; simp [coeff_coeffDerivFun]

theorem coeffDerivAddHom_monomial {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (s : τ →₀ ℕ) (a : B) :
    coeffDerivAddHom D (MvPolynomial.monomial s a) = MvPolynomial.monomial s (D a) := by
  classical
  ext m
  change AddMonoidAlgebra.coeff (coeffDerivFun D _) m = _
  rw [coeff_coeffDerivFun, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

theorem coeffDerivAddHom_mul {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      simp only [MvPolynomial.monomial_mul_monomial, coeffDerivAddHom_monomial, Derivation.leibniz,
        smul_eq_mul, map_add, add_comm v u]
    | add q₁ q₂ h₁ h₂ =>
      rw [mul_add, map_add (f := _), h₁, h₂, map_add (f := _)]; ring
  | add p₁ p₂ h₁ h₂ =>
    rw [add_mul, map_add (f := _), h₁, h₂, map_add (f := _)]; ring

theorem derivation_extend_mvPolynomial :
    ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B),
      ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B),
        (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  intro B τ _ D
  refine ⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap
    (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩
  · intro x
    show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)
    exact coeffDerivAddHom_monomial D 0 x
  · intro t
    show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0
    rw [coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendMvPolynomialStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_derivation_extend_mvPolynomial : ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B), ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B), (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  first | exact @GlobalTheory.derivation_extend_mvPolynomial | exact GlobalTheory.derivation_extend_mvPolynomial | (intros; apply GlobalTheory.derivation_extend_mvPolynomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataIterated

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

open MvPolynomial in
theorem derivation_sumAlgEquiv_eq_pderiv {Λ : Type} [CommRing Λ] {σ τ : Type}
    (d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ))
      (MvPolynomial τ (MvPolynomial σ Λ)))
    (h1 : ∀ t x, d (Sum.inl t) x = pderiv t x)
    (h2 : ∀ s x, d (Sum.inr s) (C x) = C (pderiv s x))
    (h3 : ∀ s t, d (Sum.inr s) (X t) = 0) (u : τ ⊕ σ) (y : MvPolynomial (τ ⊕ σ) Λ) :
    d u (sumAlgEquiv Λ τ σ y) = sumAlgEquiv Λ τ σ (pderiv u y) := by
  classical
  have eC : ∀ a : Λ, sumAlgEquiv Λ τ σ (C a) = C (C a) := fun a => by
    simp [sumAlgEquiv_C_inl]
  have eL : ∀ t : τ, sumAlgEquiv Λ τ σ (X (Sum.inl t)) = X t := fun t => by
    simp [sumAlgEquiv_X_inl]
  have eR : ∀ s : σ, sumAlgEquiv Λ τ σ (X (Sum.inr s)) = C (X s) := fun s => by
    simp [sumAlgEquiv_X_inr]
  have hX : ∀ v : τ ⊕ σ,
      d u (sumAlgEquiv Λ τ σ (X v)) = sumAlgEquiv Λ τ σ (pderiv u (X v)) := by
    intro v
    rcases u with t | s <;> rcases v with t' | s'
    · rw [eL, h1]
      by_cases h : t = t'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero]
    · rw [eR, h1, pderiv_C, pderiv_X_of_ne (by simp), map_zero]
    · rw [eL, h3, pderiv_X_of_ne (by simp), map_zero]
    · rw [eR, h2]
      by_cases h : s = s'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero,
          map_zero]
  induction y using MvPolynomial.induction_on with
  | C a =>
    rw [eC, pderiv_C, map_zero]
    rcases u with t | s
    · rw [h1, pderiv_C]
    · rw [h2, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hX, map_add (f := _), smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]

theorem exists_generic_jacobian_data_iterated : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  intro Λ _ _ _ _ σ τ _ _ Q _ hQ d h1 h2 h3
  let e := MvPolynomial.sumAlgEquiv Λ τ σ
  have eC : ∀ a : Λ, e (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := fun a => by
    simp [e, MvPolynomial.sumAlgEquiv_C_inl]
  obtain ⟨h, f, s, g, hg, hf, hx, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (τ ⊕ σ) (Q.comap e)
    (fun a ha => hQ a (by rw [← eC]; exact ha))
  refine ⟨h, fun j => e (f j), s, e g, hg, hf, fun x hxQ => ?_, ?_⟩
  · have h4 := hx (e.symm x) (by simpa [Ideal.mem_comap] using hxQ)
    have h5 := Ideal.mem_map_of_mem e h4
    rw [Ideal.map_span, ← Set.range_comp, map_mul, AlgEquiv.apply_symm_apply] at h5
    exact h5
  · intro hmem
    apply hdet
    rw [Ideal.mem_comap, AlgEquiv.map_det]
    convert hmem using 2
    ext i j : 1
    exact (derivation_sumAlgEquiv_eq_pderiv d h1 h2 h3 _ _).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataIteratedStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_generic_jacobian_data_iterated_alt : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  first | exact @GlobalTheory.exists_generic_jacobian_data_iterated | exact GlobalTheory.exists_generic_jacobian_data_iterated | (intros; apply GlobalTheory.exists_generic_jacobian_data_iterated <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialTensorBaseChangeRingEquivStatement

section

@[expose] public section

open TensorProduct


theorem _root_.GlobalTheory.T.mvPolynomial_tensor_baseChange_ringEquiv' :
    ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K]
      [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K],
      letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) :=
        (MvPolynomial.map (algebraMap S B)).toAlgebra;
      Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  intro S B K τ _ _ _ _ _ _ _
  let : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := MvPolynomial.algebraMvPolynomial
  let e : MvPolynomial τ S ⊗[S] B ≃ₐ[MvPolynomial τ S] MvPolynomial τ B :=
    Algebra.IsPushout.equiv S (MvPolynomial τ S) B (MvPolynomial τ B)
  exact ⟨(Algebra.TensorProduct.comm (MvPolynomial τ S) (MvPolynomial τ B) K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[MvPolynomial τ S] K) e.symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange S (MvPolynomial τ S) (MvPolynomial τ S) K B).toRingEquiv.trans
        (Algebra.TensorProduct.comm S K B).toRingEquiv))⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFibreOfLiftedPartialDerivations

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem regularFibre_of_liftedPartialDerivations :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  intro Λ _ _ _ _ σ _ B K _ _ _ _ _ _ hΛ hlift
  obtain ⟨F, hF⟩ := (Algebra.essFiniteType_iff (R := MvPolynomial σ Λ) (S := K)).1 inferInstance
  let φ : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ) →ₐ[MvPolynomial σ Λ] K :=
    MvPolynomial.aeval (fun z : ↥(F : Set K) => (z : K))
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower (MvPolynomial σ Λ) (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) (MvPolynomial (↥(F : Set K)) B) :=
    (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B)).toAlgebra
  have hC : ∀ x, algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K (MvPolynomial.C x) =
      algebraMap (MvPolynomial σ Λ) K x := fun x => MvPolynomial.aeval_C _ _
  set Q := RingHom.ker (algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  have hfrac : ∀ y : K, ∃ a b : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ), b ∉ Q ∧
      y * algebraMap _ K b = algebraMap _ K a := by
    intro y
    obtain ⟨t, ht, htu, hyt⟩ := hF y
    rw [Algebra.adjoin_eq_range] at ht hyt
    obtain ⟨b, hb⟩ := ht
    obtain ⟨a, ha⟩ := hyt
    refine ⟨a, b, ?_, ?_⟩
    · rw [hQdef, RingHom.mem_ker]
      change φ b ≠ 0
      rw [show φ b = t from hb]
      exact htu.ne_zero
    · change y * φ b = φ a
      rw [show φ b = t from hb, show φ a = y * t from ha]
  have hΛQ : ∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0 := by
    intro a ha
    rw [hQdef, RingHom.mem_ker, hC] at ha
    exact hΛ a ha
  choose Dσ hDσ using hlift
  choose dσ hdσC hdσX using fun s : σ => GlobalTheory.T.exists_derivation_extend_mvPolynomial (MvPolynomial σ Λ) (↥(F : Set K))
    ((MvPolynomial.pderiv s : Derivation Λ (MvPolynomial σ Λ) (MvPolynomial σ Λ)).restrictScalars ℤ)
  choose Eσ hEσC hEσX using fun s : σ => GlobalTheory.T.exists_derivation_extend_mvPolynomial B (↥(F : Set K)) (Dσ s)
  let d : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ))
      (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) dσ
  let D : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) B) (MvPolynomial (↥(F : Set K)) B) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) Eσ
  have hcompat : ∀ u x, D u (algebraMap _ (MvPolynomial (↥(F : Set K)) B) x) =
      algebraMap _ (MvPolynomial (↥(F : Set K)) B) (d u x) := by
    intro u x
    change D u (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) x) =
      MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) (d u x)
    rcases u with t | s
    · exact MvPolynomial.pderiv_map
    · change Eσ s _ = MvPolynomial.map _ (dσ s x)
      induction x using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.map_C, hEσC, hDσ, hdσC, MvPolynomial.map_C]
        rfl
      | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
      | mul_X p t ih =>
        rw [map_mul, Derivation.leibniz, Derivation.leibniz, MvPolynomial.map_X, hEσX, hdσX, ih]
        simp [smul_eq_mul]
  obtain ⟨h, f, s, g, hg, hfQ, hQspan, hdet⟩ :=
    GlobalTheory.T.exists_generic_jacobian_data_iterated_alt Λ σ (↥(F : Set K)) Q hΛQ d (fun t x => rfl) (fun s x => hdσC s x) (fun s t => hdσX s t)
  have hreg : IsRegularRing (MvPolynomial (↥(F : Set K)) B ⊗[MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)] K) :=
    GlobalTheory.T.isRegular_fibre_of_jacobian_derivations _ _ K Q rfl hfrac h f g (fun i => d (s i)) (fun i => D (s i))
      (fun i x => hcompat (s i) x) hg hfQ hQspan hdet
  obtain ⟨e⟩ := GlobalTheory.T.mvPolynomial_tensor_baseChange_ringEquiv' (MvPolynomial σ Λ) B K (↥(F : Set K))
  exact IsRegularRing.of_ringEquiv e

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFibreOfLiftedPartialDerivationsStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.regular_fibre_of_lifted_partialDerivations : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  first | exact @GlobalTheory.regularFibre_of_liftedPartialDerivations | exact GlobalTheory.regularFibre_of_liftedPartialDerivations | (intros; apply GlobalTheory.regularFibre_of_liftedPartialDerivations <;> assumption)
end
end
