module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsWitnessesOfFormallySmoothQuotient
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormal

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothRel

theorem derivation_mem_of_mem_sq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) : D x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact I.add_mem (I.mul_mem_right _ hy) (I.mul_mem_right _ hz)
  · rw [map_add (f := _)]; exact I.add_mem hy hz

theorem taylor_rem_mem {R σ : Type} [CommRing R] [Fintype σ] (I : Ideal (MvPolynomial σ R))
    (u : σ → MvPolynomial σ R) (hu : ∀ i, u i ∈ I) (h : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + u i) h - h
      - ∑ i, MvPolynomial.pderiv i h * u i ∈ I ^ 2 := by
  classical
  induction h using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := Ideal.add_mem _ hp hq
    convert this using 1
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]; ring
  | mul_X p s hp =>
    have hD : ∑ i, MvPolynomial.pderiv i p * u i ∈ I :=
      Ideal.sum_mem _ fun i _ ↦ I.mul_mem_left _ (hu i)
    have h2 : (∑ i, MvPolynomial.pderiv i p * u i) * u s ∈ I ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hD (hu s)
    have h3 := Ideal.add_mem _ h2 ((I ^ 2).mul_mem_left (MvPolynomial.X s + u s) hp)
    have hs : ∑ i, MvPolynomial.pderiv i (p * MvPolynomial.X s) * u i
        = p * u s + MvPolynomial.X s * ∑ i, MvPolynomial.pderiv i p * u i := by
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · simp [Pi.single_apply]
      · exact Finset.sum_congr rfl fun i _ => by ring
    convert h3 using 1
    rw [map_mul, MvPolynomial.aeval_X, hs]; ring

theorem relations_combination :
    ∀ (R₀ : Type) [CommRing R₀] (n r : ℕ) (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (b : Fin r → Fin r → Fin r → MvPolynomial (Fin n) R₀), (∀ j, MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) → (∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2) ∧ ∀ j m, MvPolynomial.pderiv m (g j) + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * MvPolynomial.pderiv m (g k) ∈ Ideal.span (Set.range g) := by
  intro R₀ _ n r g a b hrel
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  have hg : ∀ k, g k ∈ J := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hu : ∀ i, (∑ k, a i k * g k) ∈ J := fun i =>
    Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hg k)
  have h1 : ∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ J ^ 2 := by
    intro j
    have hT := taylor_rem_mem J (fun i => ∑ k, a i k * g k) hu (g j)
    have hA : MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) ∈ J ^ 2 := by
      rw [hrel j]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        (J ^ 2).mul_mem_left _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hg k) (hg l))
    have := Ideal.sub_mem _ hA hT
    convert this using 1
    ring
  refine ⟨h1, fun j m => ?_⟩
  have hF := derivation_mem_of_mem_sq (MvPolynomial.pderiv m) J (h1 j)
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hg k)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hF ⊢

  simpa [Derivation.leibniz, map_sum, map_add (f := _), map_mul, hg0, smul_eq_mul, mul_add,
  Finset.sum_add_distrib] using hF

end GlobalTheory.SmoothRel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smoothPresentation_relations_combination_normal : ∀ (R₀ : Type) [CommRing R₀] (n r : ℕ) (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (b : Fin r → Fin r → Fin r → MvPolynomial (Fin n) R₀), (∀ j, MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) → (∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2) ∧ ∀ j m, MvPolynomial.pderiv m (g j) + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * MvPolynomial.pderiv m (g k) ∈ Ideal.span (Set.range g) := by
  first | exact @GlobalTheory.SmoothRel.relations_combination | exact GlobalTheory.SmoothRel.relations_combination | (intros; apply GlobalTheory.SmoothRel.relations_combination <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmooth

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmoothRetract

open MvPolynomial

variable {R₀ : Type} [CommRing R₀] {n r : ℕ}

def tang (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i l : Fin n) : MvPolynomial (Fin n) R₀ :=
  (if i = l then 1 else 0) + ∑ k, a i k * pderiv l (g k)

def rel (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) R₀ :=
  rename Sum.inr (∑ k, a i k * g k) +
    ∑ l, rename Sum.inr (tang g a i l) * (X (Sum.inl l) - X (Sum.inr l))

theorem aeval_pderiv_rel (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) {B : Type} [CommRing B] [Algebra R₀ B]
    (xb : Fin n → B) (hg : ∀ k, aeval xb (g k) = 0) (i j : Fin n) :
    aeval (Sum.elim xb xb) (pderiv (Sum.inr i) (rel g a j)) = -(if i = j then 1 else 0) := by
  classical
  simp [rel, Derivation.leibniz, pderiv_rename Sum.inr_injective, pderiv_X, Pi.single_apply,
    aeval_rename, Function.comp_def, hg, tang, Finset.sum_add_distrib, mul_add, add_mul]
  exact if_congr eq_comm rfl rfl

theorem sum_pderiv_mul_tang (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (j : Fin r) (l : Fin n) :
    ∑ i, pderiv i (g j) * tang g a i l =
      pderiv l (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv l (g k) := by
  classical
  simp [tang, mul_add, Finset.sum_add_distrib]

theorem core (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (h1 : ∀ j, g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2)
    (h2 : ∀ j m, pderiv m (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv m (g k) ∈
      Ideal.span (Set.range g)) :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀)
      (i : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g))),
      Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  classical
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  set K : Ideal (MvPolynomial (Fin n ⊕ Fin n) R₀) := Ideal.span (Set.range (rel g a)) with hK
  let xb : Fin n → MvPolynomial (Fin n) R₀ ⧸ J := fun l => Ideal.Quotient.mk J (X l)
  have hxb : ∀ p, aeval xb p = Ideal.Quotient.mk J p := fun p =>
    AlgHom.congr_fun (MvPolynomial.algHom_ext (f := aeval xb) (g := Ideal.Quotient.mkₐ R₀ J)
      fun l => by simp [xb]) p
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)
  let r₀' : MvPolynomial (Fin n ⊕ Fin n) R₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    aeval (Sum.elim xb xb)
  have hren : ∀ p, r₀' (rename Sum.inr p) = Ideal.Quotient.mk J p := fun p => by
    simp [r₀', aeval_rename, Function.comp_def, ← hxb]
  have hs0 : ∀ l, r₀' (X (Sum.inl l) - X (Sum.inr l)) = 0 := fun l => by simp [r₀']
  have hrel : ∀ i, r₀' (rel g a i) = 0 := by
    intro i

    simp only [rel, map_add (f := _), map_sum, map_mul, hren, hs0, mul_zero, Finset.sum_const_zero,
    add_zero, hg0]
  have hKle : K ≤ RingHom.ker r₀' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hrel i)
  let r₀ : (MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K) →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    Ideal.Quotient.liftₐ K r₀' (fun x hx => hKle hx)
  have hr₀ : ∀ p, r₀ (Ideal.Quotient.mk K p) = r₀' p := fun p => rfl
  let P := Algebra.PreSubmersivePresentation.naive (v := rel g a) Sum.inr Sum.inr_injective
  have hval : ∀ v, P.val v = Ideal.Quotient.mk K (X v) := fun v => by
    simp [P]
    rfl
  have hr₀alg : ∀ p, r₀ (algebraMap P.Ring _ p) = r₀' p := by
    intro p
    rw [Algebra.Generators.algebraMap_apply]
    have : r₀.comp (aeval P.val) = r₀' :=
      MvPolynomial.algHom_ext fun v => by simp [hval, hr₀]
    exact AlgHom.congr_fun this p
  have hjac : IsUnit (r₀ P.jacobian) := by
    rw [P.jacobian_eq_jacobiMatrix_det, hr₀alg]
    have hM : r₀'.toRingHom.mapMatrix P.jacobiMatrix = -1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply,
        Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      change aeval (Sum.elim xb xb) _ = _
      rw [aeval_pderiv_rel g a xb (fun k => by rw [hxb, hg0])]
      simp [Matrix.one_apply]
    have : r₀' P.jacobiMatrix.det = (r₀'.toRingHom.mapMatrix P.jacobiMatrix).det :=
      RingHom.map_det _ _
    rw [this, hM, Matrix.det_neg, Matrix.det_one, _root_.mul_one]
    exact (isUnit_one.neg).pow _
  let D := MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K
  let T1 := Localization.Away P.jacobian
  haveI hT1 : Algebra.IsStandardSmooth R₀ T1 := by
    let Q := Algebra.SubmersivePresentation.localizationAway T1 P.jacobian
    let P' : Algebra.SubmersivePresentation R₀ T1 (Unit ⊕ (Fin n ⊕ Fin n)) (Unit ⊕ Fin n) :=
      { __ := Q.toPreSubmersivePresentation.comp P
        jacobian_isUnit := by
          rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
            Algebra.smul_def]
          exact (IsLocalization.Away.algebraMap_isUnit _).mul Q.jacobian_isUnit }
    exact P'.isStandardSmooth
  let r₁ : T1 →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom P.jacobian (f := r₀) hjac
  have hr₁ : ∀ y, r₁ (algebraMap D T1 y) = r₀ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _

  let φ : MvPolynomial (Fin n) R₀ →+* D :=
    (Ideal.Quotient.mk K).comp (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀).toRingHom
  have hφ : ∀ p, φ p = Ideal.Quotient.mk K (rename Sum.inr p) := fun p => rfl
  let G : Fin r → D := fun k => φ (g k)
  let s : Fin n → D := fun l => Ideal.Quotient.mk K (X (Sum.inl l) - X (Sum.inr l))
  let JD : Ideal D := Ideal.span (Set.range G)
  let L : Ideal D := JD ⊔ Ideal.span (Set.range s)
  have hJD : J.map φ = JD := by
    simp only [hJ, Ideal.map_span, JD, G, ← Set.range_comp]
    rfl
  have hrelD : ∀ i, φ (∑ k, a i k * g k) + ∑ l, φ (tang g a i l) * s l = 0 := by
    intro i
    have : Ideal.Quotient.mk K (rel g a i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    rw [← this]

    simp only [rel, map_add (f := _), map_sum, map_mul, hφ, s]
  have key : ∀ j, G j ∈ L * JD := by
    intro j
    have e1 : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) =
        G j + ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) := by

      rw [map_add (f := _), map_sum]
      simp only [map_mul, G]
    have hs : ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) +
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by rw [← mul_add, hrelD i, mul_zero]
    have e3 : ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) =
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l := by

      simp only [map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have eq : G j = φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) +
        ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) := by
      rw [e3]
      linear_combination -e1 - hs
    rw [eq]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun l _ => ?_)
    · have : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) ∈ JD ^ 2 := by
        rw [← hJD, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem φ (h1 j)
      rw [pow_two] at this
      exact Ideal.mul_mono_left le_sup_left this
    · refine Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩)) ?_
      rw [sum_pderiv_mul_tang, ← hJD]
      exact Ideal.mem_map_of_mem φ (h2 j l)
  obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul L JD
    (Submodule.fg_span (Set.finite_range G)) (by
      rw [Ideal.smul_eq_mul]
      exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact key j))
  have hL : L ≤ RingHom.ker r₀ := by
    refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      change r₀ (Ideal.Quotient.mk K (rename Sum.inr (g k))) = 0
      rw [hr₀, hren, hg0]
    · rintro _ ⟨l, rfl⟩
      change r₀ (Ideal.Quotient.mk K _) = 0
      rw [hr₀, hs0]
  have hre : r₀ e = 1 := by
    have := hL he1
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact this
  let C₀ := Localization.Away (algebraMap D T1 e)
  haveI : Algebra.IsStandardSmooth T1 C₀ :=
    Algebra.IsStandardSmooth.localization_away (algebraMap D T1 e)
  have hC : Algebra.IsStandardSmooth R₀ C₀ := Algebra.IsStandardSmooth.trans R₀ T1 C₀
  let r₂ : C₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom (algebraMap D T1 e) (f := r₁) (by rw [hr₁, hre]; exact isUnit_one)
  have hr₂ : ∀ y, r₂ (algebraMap T1 C₀ y) = r₁ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _
  let ψ : D →ₐ[R₀] C₀ := (IsScalarTower.toAlgHom R₀ T1 C₀).comp (IsScalarTower.toAlgHom R₀ D T1)
  have hψe : IsUnit (ψ e) := IsLocalization.Away.algebraMap_isUnit (algebraMap D T1 e)
  have hψG : ∀ k, ψ (G k) = 0 := by
    intro k
    have h0 : e * G k = 0 := he (G k) (Ideal.subset_span ⟨k, rfl⟩)
    have : ψ e * ψ (G k) = 0 := by rw [← map_mul, h0, map_zero]
    exact (hψe.mul_right_eq_zero).1 this
  have hJle : J ≤ RingHom.ker (ψ.comp ((Ideal.Quotient.mkₐ R₀ K).comp
      (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀))) :=
    Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hψG k)
  let i : (MvPolynomial (Fin n) R₀ ⧸ J) →ₐ[R₀] C₀ :=
    Ideal.Quotient.liftₐ J _ (fun x hx => hJle hx)
  refine ⟨C₀, inferInstance, inferInstance, i, r₂, hC, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change r₂ (algebraMap T1 C₀ (algebraMap D T1 (Ideal.Quotient.mk K (rename Sum.inr p)))) = _
  rw [hr₂, hr₁, hr₀, hren]

theorem exists_retract_isStandardSmooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀],
    Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  intro R₀ B₀ _ _ _ hsm
  obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R₀) (A := B₀)
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  let e : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀] B₀ :=
    (Ideal.quotientEquivAlgOfEq R₀ hg).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  haveI : Algebra.FormallySmooth R₀ (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) :=
    Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨a, b, hab⟩ :=
    GlobalTheory.exists_witnesses_of_formallySmooth_quotient (Fin n) R₀ r g inferInstance
  obtain ⟨h1, h2⟩ := GlobalTheory.T.smoothPresentation_relations_combination_normal R₀ n r g a b hab
  obtain ⟨C₀, i1, i2, i, ρ, hstd, hret⟩ := core g a h1 h2
  exact ⟨C₀, i1, i2, i.comp e.symm.toAlgHom, e.toAlgHom.comp ρ, hstd, fun x => by simp [hret]⟩

end GlobalTheory.SmoothRetract
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmoothStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_standardSmooth_retract_of_smooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀) (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  first | exact @GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | exact GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | (intros; apply GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth <;> assumption)
end
end
