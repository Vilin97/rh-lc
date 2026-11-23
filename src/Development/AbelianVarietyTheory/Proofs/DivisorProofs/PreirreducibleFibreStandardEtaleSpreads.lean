module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreadsStatement
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Tactic.Continuity
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceFibreHypersurfaceSpectrumIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.FibreHyp

section defs
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]

abbrev Ik : Ideal (MvPolynomial σ k) := Ideal.span {MvPolynomial.map (algebraMap A k) f}

abbrev Lk := Localization.Away (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))

abbrev LA := Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)

def rhoK : MvPolynomial σ k →ₐ[k] Lk f g k :=
  (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mkₐ k (Ik f k))

def rhoA : MvPolynomial σ A →ₐ[A] LA f g :=
  (IsScalarTower.toAlgHom A (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g)).comp
    (Ideal.Quotient.mkₐ A (Ideal.span {f}))

lemma rhoK_apply (p : MvPolynomial σ k) :
    rhoK f g k p = algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k) (Ideal.Quotient.mk (Ik f k) p) := rfl

lemma rhoA_apply (p : MvPolynomial σ A) :
    rhoA f g p = algebraMap (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g) (Ideal.Quotient.mk _ p) := rfl

def fwd0 : MvPolynomial σ A →ₐ[A] Lk f g k :=
  MvPolynomial.aeval (fun i => rhoK f g k (MvPolynomial.X i))

lemma fibreHypersurfaceForwardPolynomial_apply (p : MvPolynomial σ A) :
    fwd0 f g k p = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [fwd0, ← MvPolynomial.aeval_map_algebraMap k]
  conv_rhs => rw [MvPolynomial.aeval_unique (rhoK f g k)]
  rfl

def fwd1 : (MvPolynomial σ A ⧸ Ideal.span {f}) →ₐ[A] Lk f g k :=
  Ideal.Quotient.liftₐ (Ideal.span {f}) (fwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceForwardPolynomial_apply f g k f]
    have : rhoK f g k (MvPolynomial.map (algebraMap A k) f) = 0 := by
      simp [rhoK, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, mul_zero])

lemma fibreHypersurfaceForwardQuotient_mk (p : MvPolynomial σ A) :
    fwd1 f g k (Ideal.Quotient.mk _ p) = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [← fibreHypersurfaceForwardPolynomial_apply]; rfl

def fwd2 : LA f g →ₐ[A] Lk f g k :=
  IsLocalization.Away.liftAlgHom (S := LA f g) (Ideal.Quotient.mk (Ideal.span {f}) g) (f := fwd1 f g k) (by
    rw [fibreHypersurfaceForwardQuotient_mk, rhoK_apply]
    exact IsLocalization.Away.algebraMap_isUnit (S := Lk f g k)
      (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)))

def fwd : k ⊗[A] LA f g →ₐ[k] Lk f g k :=
  Algebra.TensorProduct.lift (Algebra.ofId k _) (fwd2 f g k) (fun _ _ => Commute.all _ _)

def bwd0 : MvPolynomial σ k →ₐ[k] k ⊗[A] LA f g :=
  MvPolynomial.aeval (fun i => Algebra.TensorProduct.includeRight (rhoA f g (MvPolynomial.X i)))

lemma fibreHypersurfaceBackwardPolynomial_map (p : MvPolynomial σ A) :
    bwd0 f g k (MvPolynomial.map (algebraMap A k) p) =
      Algebra.TensorProduct.includeRight (R := A) (A := k) (rhoA f g p) := by
  letI : IsScalarTower A k (k ⊗[A] LA f g) := TensorProduct.isScalarTower_left
  rw [bwd0, MvPolynomial.aeval_map_algebraMap]
  change _ = ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g)) p
  conv_rhs => rw [MvPolynomial.aeval_unique ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g))]
  rfl

def bwd1 : (MvPolynomial σ k ⧸ Ik f k) →ₐ[k] k ⊗[A] LA f g :=
  Ideal.Quotient.liftₐ _ (bwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceBackwardPolynomial_map]
    have : rhoA f g f = 0 := by
      simp [rhoA, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, map_zero, mul_zero])

lemma fibreHypersurfaceBackwardQuotient_mk (p : MvPolynomial σ k) : bwd1 f g k (Ideal.Quotient.mk _ p) = bwd0 f g k p := rfl

def bwd2 : Lk f g k →ₐ[k] k ⊗[A] LA f g :=
  IsLocalization.Away.liftAlgHom (S := Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)) (f := bwd1 f g k) (by
    rw [fibreHypersurfaceBackwardQuotient_mk, fibreHypersurfaceBackwardPolynomial_map, rhoA_apply]
    exact (IsLocalization.Away.algebraMap_isUnit (S := LA f g)
      (Ideal.Quotient.mk (Ideal.span {f}) g)).map (Algebra.TensorProduct.includeRight (R := A) (A := k)))

lemma fwd_bwd : (fwd f g k).comp (bwd2 f g k) = AlgHom.id k _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have h1 := fibreHypersurfaceForwardQuotient_mk f g k (MvPolynomial.X i)
  have h2 := fibreHypersurfaceBackwardPolynomial_map f g k (MvPolynomial.X i)
  simp only [MvPolynomial.map_X, rhoK_apply, rhoA_apply] at h1 h2
  change fwd f g k (bwd2 f g k (algebraMap _ (Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.X i)))) =
    algebraMap _ (Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.X i))
  simp only [bwd2, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    fibreHypersurfaceBackwardQuotient_mk, h2, Algebra.TensorProduct.includeRight_apply, fwd, Algebra.TensorProduct.lift_tmul, map_one,
    _root_.one_mul, fwd2, h1]

lemma bwd_fwd : (bwd2 f g k).comp (fwd f g k) = AlgHom.id k _ := by
  letI : IsScalarTower A k (k ⊗[A] LA f g) := TensorProduct.isScalarTower_left
  apply Algebra.TensorProduct.ext
  · ext
  · apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {f}) g))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    have h1 := fibreHypersurfaceForwardQuotient_mk f g k (MvPolynomial.X i)
    have h2 := fibreHypersurfaceBackwardPolynomial_map f g k (MvPolynomial.X i)
    simp only [MvPolynomial.map_X, rhoK_apply, rhoA_apply] at h1 h2
    change bwd2 f g k (fwd f g k ((1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i)))) =
      (1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i))
    simp only [fwd, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul, fwd2, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, bwd2, fibreHypersurfaceBackwardQuotient_mk, h2,
      Algebra.TensorProduct.includeRight_apply]

lemma rhoK_comp : (rhoK f g k).toRingHom =
    (algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mk (Ik f k)) := rfl

theorem isEmbedding_comap_rhoK : Topology.IsEmbedding (PrimeSpectrum.comap (rhoK f g k).toRingHom) := by
  rw [rhoK_comp, PrimeSpectrum.comap_comp]
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding.comp
    (PrimeSpectrum.localization_away_isOpenEmbedding (Lk f g k)
      (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))).isEmbedding

theorem range_comap_rhoK : Set.range (PrimeSpectrum.comap (rhoK f g k).toRingHom) =
    PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
      PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      have : (rhoK f g k).toRingHom (MvPolynomial.map (algebraMap A k) f) = 0 := by
        simp [rhoK_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
      rw [this]; exact q.asIdeal.zero_mem
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      intro h
      have hu : IsUnit ((rhoK f g k).toRingHom (MvPolynomial.map (algebraMap A k) g)) :=
        IsLocalization.Away.algebraMap_isUnit (S := Lk f g k)
          (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  · rintro ⟨hf, hg⟩
    have h1 : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ik f k))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.zeroLocus_span]
      exact hf
    obtain ⟨q0, rfl⟩ := h1
    have h2 : q0 ∈ Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Lk f g k)
        (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))]
      intro h
      apply hg
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      exact h
    obtain ⟨q, rfl⟩ := h2
    exact ⟨q, by rw [rhoK_comp, PrimeSpectrum.comap_comp_apply]⟩

end defs

theorem preirreducibleSpace_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    PreirreducibleSpace X ↔ PreirreducibleSpace Y := by
  have key : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y),
      PreirreducibleSpace X → PreirreducibleSpace Y := by
    intro X Y _ _ e h
    refine ⟨?_⟩
    have := (PreirreducibleSpace.isPreirreducible_univ (X := X)).image e e.continuous.continuousOn
    rwa [Set.image_univ_of_surjective e.surjective] at this
  exact ⟨key e, key e.symm⟩

theorem spectrum_fibre_preirreducible_iff (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A)
    (k : Type) [Field k] [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔
      IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
        PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by
  let e : (k ⊗[A] LA f g) ≃ₐ[k] Lk f g k :=
    AlgEquiv.ofAlgHom (fwd f g k) (bwd2 f g k) (fwd_bwd f g k) (bwd_fwd f g k)
  rw [preirreducibleSpace_congr (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv), ← range_comap_rhoK,
    isPreirreducible_iff_preirreducibleSpace]
  exact preirreducibleSpace_congr (isEmbedding_comap_rhoK f g k).toHomeomorph

end GlobalTheory.FibreHyp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff : ∀ (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔ IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by
  first | exact @GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff | exact GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff | (intros; apply GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEtaleMvPolynomialHypersurface

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

open MvPolynomial in
theorem optionEquivLeft_pderiv_none (A : Type) [CommRing A] (n : ℕ)
    (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft A (Fin n) (pderiv none p) = Polynomial.derivative (optionEquivLeft A (Fin n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with _ | j
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_none, mul_comm]
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_some, pderiv_X, mul_comm]

open MvPolynomial in
theorem eval_map_eq_eval₂_optionEquivLeft (A : Type) [CommRing A] (n : ℕ) {k : Type} [Field k]
    (ψ : A →+* k) (Q : Option (Fin n) → k) (p : MvPolynomial (Option (Fin n)) A) :
    eval Q (map ψ p) = Polynomial.eval₂ (eval₂Hom ψ (Q ∘ some)) (Q none) (optionEquivLeft A (Fin n) p) := by
  rw [MvPolynomial.eval_map]
  change eval₂Hom ψ Q p = (Polynomial.eval₂RingHom (eval₂Hom ψ (Q ∘ some)) (Q none)).comp
    (optionEquivLeft A (Fin n)).toAlgHom.toRingHom p
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [optionEquivLeft_C]
  · rcases i with _ | j <;> simp [optionEquivLeft_X_none, optionEquivLeft_X_some]

open MvPolynomial in
theorem optionEquivLeft_map (A : Type) [CommRing A] (n : ℕ) {k : Type} [Field k]
    (ψ : A →+* k) (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft k (Fin n) (map ψ p) = Polynomial.map (map ψ) (optionEquivLeft A (Fin n) p) := by
  change (optionEquivLeft k (Fin n)).toAlgHom.toRingHom.comp (map ψ) p =
    (Polynomial.mapRingHom (map ψ)).comp (optionEquivLeft A (Fin n)).toAlgHom.toRingHom p
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [optionEquivLeft_C]
  · rcases i with _ | j <;> simp [optionEquivLeft_X_none, optionEquivLeft_X_some]


open MvPolynomial in
theorem standardEtale_mvPolynomial_hypersurface :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
      [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B],
      Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B →
      ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k),
        MvPolynomial.map ψ f ≠ 0) ∧
      (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k),
        MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 →
        MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧
      Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  intro A B _ _ _ n _ _ hB
  obtain ⟨P⟩ := hB.nonempty_standardEtalePresentation
  set e := optionEquivLeft A (Fin n) with he
  refine ⟨e.symm P.f, e.symm P.g, ?_, ?_, ?_⟩
  · intro k _ ψ h
    have h1 := optionEquivLeft_map A n ψ (e.symm P.f)
    rw [h, map_zero, ← he, e.apply_symm_apply] at h1
    exact (P.monic_f.map (MvPolynomial.map ψ)).ne_zero h1.symm
  · intro k _ ψ Q hf hg
    obtain ⟨p₁, p₂, m, hc⟩ := P.cond
    set Φ := Polynomial.eval₂RingHom (eval₂Hom ψ (Q ∘ some)) (Q none)
    have key : ∀ p, eval Q (map ψ p) = Φ (e p) := fun p => eval_map_eq_eval₂_optionEquivLeft A n ψ Q p
    rw [key, e.apply_symm_apply] at hf hg
    rw [pderiv_map, key, optionEquivLeft_pderiv_none, ← he, e.apply_symm_apply]
    intro hd
    have := congrArg Φ hc
    simp only [map_add (f := _), map_mul, map_pow] at this
    change Φ (Polynomial.derivative P.f) * _ + _ = _ at this
    rw [hd, hf] at this
    simp only [zero_mul, add_zero] at this
    exact (pow_ne_zero m hg) this.symm
  · let qe : (MvPolynomial (Option (Fin n)) A ⧸ Ideal.span {e.symm P.f}) ≃ₐ[A] AdjoinRoot P.f :=
      Ideal.quotientEquivAlg _ _ e (by rw [Ideal.map_span, Set.image_singleton]; simp)
    have hM : Submonoid.map qe (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {e.symm P.f}) (e.symm P.g))) =
        Submonoid.powers (AdjoinRoot.mk P.f P.g) := by
      rw [Submonoid.map_powers]
      congr 1
      refine (Ideal.quotientEquivAlg_mk (f := e) (x := e.symm P.g) ..).trans ?_
      rw [AlgEquiv.apply_symm_apply]
      rfl
    let le := IsLocalization.algEquivOfAlgEquiv (Localization.Away (Ideal.Quotient.mk (Ideal.span {e.symm P.f}) (e.symm P.g)))
      (Localization.Away (AdjoinRoot.mk P.f P.g)) qe hM
    exact ⟨((P.equivRing.trans P.P.equivAwayAdjoinRoot).restrictScalars A).trans le.symm⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEtaleMvPolynomialHypersurfaceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.standardEtale_localization_away_quotient_span : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) ∧ (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧ Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  first | exact @GlobalTheory.standardEtale_mvPolynomial_hypersurface | exact GlobalTheory.standardEtale_mvPolynomial_hypersurface | (intros; apply GlobalTheory.standardEtale_mvPolynomial_hypersurface <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleFibreStandardEtaleSpreads

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preirreducibleSpace_of_continuous_surjective_fibreChart {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [hX : PreirreducibleSpace X] (f : X → Y) (hf : Continuous f)
    (hs : Function.Surjective f) : PreirreducibleSpace Y :=
  ⟨by simpa [Set.image_univ_of_surjective hs] using
    hX.isPreirreducible_univ.image f hf.continuousOn⟩

theorem preirreducibleSpace_tensor_congr_fibreChart (A B C k : Type) [CommRing A] [CommRing B]
    [CommRing C] [CommRing k] [Algebra A B] [Algebra A C] [Algebra A k] (e : B ≃ₐ[A] C) :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) ↔ PreirreducibleSpace (PrimeSpectrum (k ⊗[A] C)) := by
  let E : k ⊗[A] B ≃ₐ[A] k ⊗[A] C := Algebra.TensorProduct.congr AlgEquiv.refl e
  let H := PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
  constructor
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H H.continuous H.surjective
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H.symm H.symm.continuous
      H.symm.surjective

theorem preirreducibleSpace_fibre_standardEtale_spreads :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by
  intro A B _ _ _ n _ _ hB Ω _ _ _ hΩ
  obtain ⟨f, g, hf, hd, ⟨e⟩⟩ := GlobalTheory.T.standardEtale_localization_away_quotient_span A B n hB
  have hΩ' := (GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g Ω).1 ((preirreducibleSpace_tensor_congr_fibreChart A _ _ Ω e).1 hΩ)
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads A (Option (Fin n)) f g none hf hd Ω (algebraMap A Ω) hΩ'
  refine ⟨a, I, ha, hI, ?_⟩
  intro k _ _ _ hak hIk
  exact (preirreducibleSpace_tensor_congr_fibreChart A _ _ k e).2
    ((GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g k).2 (hk k (algebraMap A k) hak hIk))

end GlobalTheory
end
end
