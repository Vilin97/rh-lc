module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EvalEqZeroOfMemVanIdeal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSetOfHilbertFunctionsFibres

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

namespace HilbertFamily

open MvPolynomial

theorem finrank_tensor_eq_of_retract {A M N : Type} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (i : N →ₗ[A] M) (r : M →ₗ[A] N) (hri : r ∘ₗ i = LinearMap.id) (a : A)
    (ha : ∀ (B : Type) [CommRing B] [Algebra A B], IsUnit (algebraMap A B a) →
      Module.Free B (B ⊗[A] M))
    (K : Type) [Field K] [Algebra A K] (hK : algebraMap A K a ≠ 0) :
    Module.finrank K (K ⊗[A] N) =
      Module.finrank (FractionRing A) (FractionRing A ⊗[A] N) := by
  let p : Ideal A := RingHom.ker (algebraMap A K)
  have : p.IsPrime := RingHom.ker_isPrime _
  let B := Localization.AtPrime p
  have : Module.Free B (B ⊗[A] M) :=
    ha B (IsLocalization.map_units B (⟨a, hK⟩ : p.primeCompl))
  have : Module.Flat B (B ⊗[A] N) :=
    Module.Flat.of_retract (i.baseChange B) (r.baseChange B) (by
      rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id])
  have : Module.Free B (B ⊗[A] N) := Module.free_of_flat_of_isLocalRing
  have key : ∀ (L : Type) [Field L] [Algebra A L],
      (∀ y : p.primeCompl, IsUnit (algebraMap A L y)) →
      Module.finrank L (L ⊗[A] N) = Module.finrank B (B ⊗[A] N) := by
    intro L _ _ hL
    let : Algebra B L := (IsLocalization.lift (M := p.primeCompl) hL).toAlgebra
    have : IsScalarTower A B L :=
      .of_algebraMap_eq fun y => (IsLocalization.lift_eq (M := p.primeCompl) hL y).symm
    rw [← Module.finrank_baseChange (R := L) (S := B) (M' := B ⊗[A] N)]
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A B L L N).finrank_eq.symm
  rw [key K fun y => isUnit_iff_ne_zero.2 y.2, key (FractionRing A) fun y => ?_]
  refine isUnit_iff_ne_zero.2 ?_
  rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  intro h
  exact y.2 (h ▸ p.zero_mem)

noncomputable def piece {A σ : Type} [CommRing A] (I : Ideal (MvPolynomial σ A)) (e : ℕ) :
    Submodule A (MvPolynomial σ A ⧸ I) :=
  (homogeneousSubmodule σ A e).map (Ideal.Quotient.mkₐ A I).toLinearMap

instance {A σ : Type} [CommRing A] [Finite σ] (I : Ideal (MvPolynomial σ A)) (e : ℕ) :
    Module.Finite A (piece I e) :=
  Module.Finite.iff_fg.2 ((homogeneousSubmodule_fg σ A e).map _)

theorem exists_retract {A σ : Type} [CommRing A] (I : Ideal (MvPolynomial σ A))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ) :
    ∃ r : (MvPolynomial σ A ⧸ I) →ₗ[A] piece I e, r ∘ₗ (piece I e).subtype = LinearMap.id := by
  let f : MvPolynomial σ A →ₗ[A] piece I e :=
    LinearMap.codRestrict (piece I e)
      ((Ideal.Quotient.mkₐ A I).toLinearMap ∘ₗ homogeneousComponent e)
      fun F => ⟨_, homogeneousComponent_mem e F, rfl⟩
  have hf : I.restrictScalars A ≤ LinearMap.ker f := fun F hF =>
    Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (hI F hF e))
  refine ⟨((I.restrictScalars A).liftQ f hf) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv A I).symm.toLinearMap, ?_⟩
  ext ⟨_, F, hF, rfl⟩
  change Ideal.Quotient.mk I (homogeneousComponent e F) = Ideal.Quotient.mk I F
  simp [homogeneousComponent_of_mem hF]

theorem dimDeg_add_finrank {A σ : Type} [CommRing A] [Finite σ] (I : Ideal (MvPolynomial σ A))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ)
    (K : Type) [Field K] [Algebra A K] :
    Module.finrank K (K ⊗[A] piece I e) + ZM.dimDeg (I.map (map (algebraMap A K))) e =
      Nat.card {d : σ →₀ ℕ | d.degree = e} := by
  obtain ⟨r, hr⟩ := exists_retract I hI e
  have hinj : Function.Injective ((piece I e).subtype.baseChange K) := by
    apply Function.LeftInverse.injective (g := r.baseChange K)
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id,
      LinearMap.id_apply]
  let ε := algebraTensorAlgEquiv (σ := σ) A K
  let ψ : MvPolynomial σ K →ₗ[K] K ⊗[A] (MvPolynomial σ A ⧸ I) :=
    (Ideal.Quotient.mkₐ A I).toLinearMap.baseChange K ∘ₗ ε.symm.toLinearMap
  have hψ : ∀ F : MvPolynomial σ A, ψ (map (algebraMap A K) F) = 1 ⊗ₜ Ideal.Quotient.mk I F := by
    intro F
    have : ε.symm (map (algebraMap A K) F) = 1 ⊗ₜ F := by
      rw [AlgEquiv.symm_apply_eq, algebraTensorAlgEquiv_tmul, one_smul]
    change (Ideal.Quotient.mkₐ A I).toLinearMap.baseChange K (ε.symm _) = _
    rw [this]
    rfl
  have hker : ∀ G, ψ G = 0 ↔ G ∈ I.map (map (algebraMap A K)) := by
    intro G
    have h1 := Algebra.TensorProduct.lTensor_ker (A := K) (Ideal.Quotient.mkₐ A I)
      (Ideal.Quotient.mkₐ_surjective A I)
    have h2 : RingHom.ker (Ideal.Quotient.mkₐ A I) = I := Ideal.Quotient.mkₐ_ker A I
    rw [h2] at h1
    have h3 : (map (algebraMap A K) : MvPolynomial σ A →+* MvPolynomial σ K) =
        (ε.toRingEquiv : _ →+* _).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := K)
            (B := MvPolynomial σ A)).toRingHom := by
      refine RingHom.ext fun F => ?_
      change _ = ε (1 ⊗ₜ F)
      rw [algebraTensorAlgEquiv_tmul, one_smul]
    have h4 : I.map (Algebra.TensorProduct.includeRight (R := A) (A := K)
        (B := MvPolynomial σ A)).toRingHom = _ := h1.symm
    rw [h3, ← Ideal.map_map, h4, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker]
    rfl
  have hrange : (homogeneousSubmodule σ K e).map ψ = (piece I e).baseChange K := by
    apply le_antisymm
    · rintro _ ⟨G, hG, rfl⟩

      rw [G.as_sum, map_sum]
      refine Submodule.sum_mem _ fun d hd => ?_
      have hd' : d.degree = e := by
        rw [Finsupp.degree_eq_weight_one]
        exact hG (mem_support_iff.1 hd)
      have : (monomial d (AddMonoidAlgebra.coeff G d) : MvPolynomial σ K) =
          AddMonoidAlgebra.coeff G d • map (algebraMap A K) (monomial d 1) := by
        simp [smul_monomial]
      rw [this, map_smul, hψ]
      exact Submodule.smul_mem _ _ (Submodule.tmul_mem_baseChange_of_mem _
        ⟨_, isHomogeneous_monomial 1 hd', rfl⟩)
    · rintro _ ⟨z, rfl⟩
      induction z with
      | add z w hz hw => simpa only [map_add] using add_mem hz hw
      | tmul c n =>
        obtain ⟨_, F, hF, rfl⟩ := n
        refine ⟨c • map (algebraMap A K) F,
          Submodule.smul_mem _ _ (IsHomogeneous.map hF _), ?_⟩
        rw [map_smul, hψ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
  have : Module.Finite K (homogeneousSubmodule σ K e) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ K e)
  have h := LinearMap.finrank_range_add_finrank_ker (ψ ∘ₗ (homogeneousSubmodule σ K e).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, hrange, Submodule.baseChange,
    LinearMap.finrank_range_of_inj hinj, LinearMap.ker_comp,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h
  have hk : LinearMap.ker ψ = (I.map (map (algebraMap A K))).restrictScalars K :=
    Submodule.ext hker
  rw [hk] at h
  refine h.trans ?_
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

theorem exists_const_of_isDomain {A σ : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Finite σ] (I : Ideal (MvPolynomial σ A))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) :
    ∃ a : A, a ≠ 0 ∧ ∃ φ : ℕ → ℕ, ∀ (K : Type) [Field K] (x : A →+* K), x a ≠ 0 →
      ZM.dimDeg (I.map (map x)) = φ := by
  obtain ⟨a, ha0, ha⟩ := exists_free_tensor_of_isUnit.{0} A (MvPolynomial σ A)
    (MvPolynomial σ A ⧸ I)
  refine ⟨a, ha0, ZM.dimDeg (I.map (map (algebraMap A (FractionRing A)))), fun K _ x hx => ?_⟩
  let : Algebra A K := x.toAlgebra
  funext e
  obtain ⟨r, hr⟩ := exists_retract I hI e
  have h1 := finrank_tensor_eq_of_retract _ r hr a ha K hx
  have h2 := dimDeg_add_finrank I hI e K
  have h3 := dimDeg_add_finrank I hI e (FractionRing A)
  change ZM.dimDeg (I.map (map (algebraMap A K))) e = _
  omega

theorem finite_of_le_ker {R σ : Type} [CommRing R] [IsNoetherianRing R] [Finite σ]
    (I : Ideal (MvPolynomial σ R)) (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (J : Ideal R) :
    {φ : ℕ → ℕ | ∃ (K : Type) (_ : Field K) (x : R →+* K), J ≤ RingHom.ker x ∧
      φ = ZM.dimDeg (I.map (map x))}.Finite := by
  induction J using IsNoetherian.induction with
  | _ J ih =>
  have hlt : ∀ b, b ∉ J → J < J ⊔ Ideal.span {b} := fun b hb =>
    lt_of_le_of_ne le_sup_left fun h =>
      hb (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have hle : ∀ (K : Type) [Field K] (x : R →+* K) (b : R), J ≤ RingHom.ker x → x b = 0 →
      J ⊔ Ideal.span {b} ≤ RingHom.ker x := fun K _ x b h hb =>
    sup_le h ((Ideal.span_singleton_le_iff_mem _).2 hb)
  by_cases hJ : Ideal.IsPrime J
  · have hsurj : Function.Surjective (map (σ := σ) (Ideal.Quotient.mk J)) :=
      map_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨a, ha0, φ₀, h⟩ := exists_const_of_isDomain (I.map (map (Ideal.Quotient.mk J))) (by
      intro F hF e
      obtain ⟨G, hG, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hF
      have : homogeneousComponent e (map (Ideal.Quotient.mk J) G) =
          map (Ideal.Quotient.mk J) (homogeneousComponent e G) := by
        ext d
        simp only [coeff_homogeneousComponent, coeff_map]
        split_ifs <;> simp
      rw [this]
      exact Ideal.mem_map_of_mem _ (hI G hG e))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have haJ : a ∉ J := fun h => ha0 (Ideal.Quotient.eq_zero_iff_mem.2 h)
    refine ((ih _ (hlt a haJ)).insert φ₀).subset ?_
    rintro _ ⟨K, _, x, hx, rfl⟩
    by_cases hxa : x a = 0
    · exact Or.inr ⟨K, _, x, hle K x a hx hxa, rfl⟩
    · left
      rw [← h K (Ideal.Quotient.lift J x hx) hxa, Ideal.map_map]
      congr 2
      refine RingHom.ext fun F => ?_
      rw [RingHom.comp_apply, map_map]
      rfl
  · rcases Ideal.not_isPrime_iff.1 hJ with rfl | ⟨b, hb, c, hc, hbc⟩
    · refine Set.finite_empty.subset ?_
      rintro _ ⟨K, _, x, hx, rfl⟩
      have : x 1 = 0 := hx Submodule.mem_top
      simp at this
    · refine ((ih _ (hlt b hb)).union (ih _ (hlt c hc))).subset ?_
      rintro _ ⟨K, _, x, hx, rfl⟩
      have : x b * x c = 0 := by rw [← map_mul]; exact hx hbc
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl ⟨K, _, x, hle K x b hx h, rfl⟩
      · exact Or.inr ⟨K, _, x, hle K x c hx h, rfl⟩

end HilbertFamily


open GlobalTheory.ZM in
theorem finite_setOf_dimDeg_map : ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → {φ : ℕ → ℕ | ∃ (K : Type) (_ : Field K) (x : R →+* K), φ = dimDeg (I.map (MvPolynomial.map x))}.Finite := by
  intro R σ _ _ _ I hI
  refine (HilbertFamily.finite_of_le_ker I hI ⊥).subset ?_
  rintro _ ⟨K, _, x, rfl⟩
  exact ⟨K, _, x, bot_le, rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSetOfHilbertFunctionsFibresStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.finite_setOf_hilbertFunctions_fibres : ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → {φ : ℕ → ℕ | ∃ (K : Type) (_ : Field K) (x : R →+* K), φ = dimDeg (I.map (MvPolynomial.map x))}.Finite := by
  first | exact @GlobalTheory.finite_setOf_dimDeg_map | exact GlobalTheory.finite_setOf_dimDeg_map | (intros; apply GlobalTheory.finite_setOf_dimDeg_map <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayProjectiveFormsThroughPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FormsFamily

theorem exists_const_near {R α : Type} [CommRing R] [PartialOrder α] {P : Set (Ideal R)} (hP : DenseP P)
    (r : ∀ (K : Type) [Field K], (R →+* K) → α) (ρ : α) (g : R)
    (hsc : ∀ (K : Type) [Field K] (x : R →+* K), ∃ f : R, x f ≠ 0 ∧
      ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y ≤ r K x)
    (hρ : ∀ q ∈ P, g ∉ q → ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ r K x = ρ)
    (K : Type) [Field K] (x : R →+* K) (hg : x g ≠ 0) (hx : r K x = ρ) :
    ∃ f : R, x f ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y = ρ := by
  obtain ⟨f, hf, h⟩ := hsc K x
  refine ⟨f * g, by rw [map_mul]; exact mul_ne_zero hf hg, fun L _ y hy => ?_⟩
  rw [map_mul] at hy
  refine le_antisymm (hx ▸ h L y (left_ne_zero_of_mul hy)) ?_
  obtain ⟨f', hf', h'⟩ := hsc L y
  have h0 : f' * g ≠ 0 := fun h0 => mul_ne_zero hf' (right_ne_zero_of_mul hy) (by rw [← map_mul, h0, map_zero])
  have h1 : ¬ ∀ q ∈ P, q.IsPrime → f' * g ∈ q := fun h1 => h0 (hP _ h1)
  push Not at h1
  obtain ⟨q, hq, -, hq'⟩ := h1
  obtain ⟨K', _, x', rfl, rfl⟩ := hρ q hq fun h2 => hq' (q.mul_mem_left _ h2)
  exact h' K' x' fun h2 => hq' (Ideal.mul_mem_right _ _ h2)

theorem exists_away_projective_vanIdeal : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ (∀ e ≥ d, Module.Projective (Localization.Away f) (↥(MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e) ⧸ ((vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).restrictScalars (Localization.Away f)).comap (MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e).subtype)) ∧ ∀ (K : Type) [Field K] (x : (Localization.Away f) →+* K), (vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).map (MvPolynomial.map x) = vanIdeal d (fun h i => x ((algebraMap R (Localization.Away f)) (p h i))) := by
  intro R _ _ _ σ Hh _ _ p Q d P hP hcut q₀ hq₀
  classical
  obtain ⟨K₀, _, x₀, I₀, rfl, hc₀⟩ := hcut q₀ hq₀
  have hI := component_mem_vanIdeal d p
  obtain ⟨f₁, hf₁, h₁⟩ := exists_const_near hP
    (fun K _ x => (dimDeg (vanIdeal d fun h i => x (p h i)) d : ℚ)) (Q.eval (d : ℚ)) 1
    (fun K _ x => (exists_dimDeg_vanIdeal_le d p K x).imp fun f hf =>
      ⟨hf.1, fun L _ y hy => Nat.cast_le.2 (hf.2 L y hy)⟩)
    (fun q hq _ => by
      obtain ⟨K, _, x, I, hx, hc⟩ := hcut q hq
      exact ⟨K, _, x, hx, dimDeg_eq_of_cutBy hc le_rfl⟩)
    K₀ x₀ (by simp) (dimDeg_eq_of_cutBy hc₀ le_rfl)
  have h₂ := map_vanIdeal_of_const_away d p _ f₁ h₁
  have h₃ : ∀ e ≥ d, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      (dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) e : ℚ) = Q.eval (e : ℚ) := by
    intro e he
    obtain ⟨g, hg, h⟩ := exists_const_near hP
      (fun K _ x => -(dimDeg ((vanIdeal d p).map (MvPolynomial.map x)) e : ℚ)) (-Q.eval (e : ℚ)) f₁
      (fun K _ x => (exists_dimDeg_map_le _ hI e K x).imp fun f hf =>
        ⟨hf.1, fun L _ y hy => neg_le_neg (Nat.cast_le.2 (hf.2 L y hy))⟩)
      (fun q hq hq' => by
        obtain ⟨K, _, x, I, rfl, hc⟩ := hcut q hq
        exact ⟨K, _, x, rfl, by rw [h₂ K x hq', dimDeg_eq_of_cutBy hc he]⟩)
      K₀ x₀ hf₁ (by rw [h₂ K₀ x₀ hf₁, dimDeg_eq_of_cutBy hc₀ he])
    exact ⟨g, hg, fun L _ y hy => neg_injective (h L y hy)⟩
  have h₄ : ∀ φ : ℕ → ℕ, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      φ = dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) → ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ) := by
    intro φ
    by_cases hφ : ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ)
    · exact ⟨1, by simp, fun _ _ _ _ _ => hφ⟩
    · push Not at hφ
      obtain ⟨e, he, hne⟩ := hφ
      obtain ⟨g, hg, h⟩ := h₃ e he
      exact ⟨g, hg, fun L _ y hy hφ => absurd (hφ ▸ h L y hy) hne⟩
  choose g hg h₅ using h₄
  have hfin := GlobalTheory.T.finite_setOf_hilbertFunctions_fibres R σ (vanIdeal d p) hI
  let f : R := f₁ * ∏ φ ∈ hfin.toFinset, g φ
  have h₆ : ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (p h i)) e : ℚ) = Q.eval (e : ℚ) := by
    intro L _ y hy
    simp only [f, map_mul, map_prod, ne_eq, mul_eq_zero, not_or] at hy
    rw [← h₂ L y hy.1]
    exact h₅ _ L y (Finset.prod_ne_zero_iff.1 hy.2 _ (hfin.mem_toFinset.2 ⟨L, _, y, rfl⟩)) rfl
  have hf : f ∉ RingHom.ker x₀ := by
    rw [RingHom.mem_ker, map_mul, map_prod]
    exact mul_ne_zero hf₁ (Finset.prod_ne_zero_iff.2 fun φ _ => hg φ)
  haveI : IsReduced (Localization.Away f) :=
    isReduced_localizationPreserves (Submonoid.powers f) _ inferInstance
  have h₇ : ∀ (L : Type) [Field L] (y : Localization.Away f →+* L), ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (algebraMap R (Localization.Away f) (p h i))) e : ℚ) = Q.eval (e : ℚ) :=
    fun L _ y => h₆ L (y.comp (algebraMap R _))
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map y).ne_zero
  have h₈ := map_vanIdeal_of_const d (fun h i => algebraMap R (Localization.Away f) (p h i)) _
    fun L _ y => h₇ L y d le_rfl
  exact ⟨f, hf, fun e he => projective_of_const _ (component_mem_vanIdeal d _) e (Q.eval (e : ℚ))
    fun L _ y => by rw [h₈ L y]; exact h₇ L y e he, fun K _ x => h₈ K x⟩

end GlobalTheory.ZM.FormsFamily
end
end
