module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseSectionsOfAlgebraicAffineNbhdStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalRing.Module
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyVanishingOfFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleChartSmoothAlgebraLocalPoint

section

@[expose] public section

open IsLocalRing

noncomputable section
namespace GlobalTheory.DenseSec

open KaehlerDifferential
open scoped TensorProduct

theorem formallyEtale_of_bijective_kaehler_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem exists_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A),
      (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  intro R _ _ A _ _ _ ε
  classical
  let p : Ideal A := (maximalIdeal R).comap ε
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let t : κ → A := fun i => a i - algebraMap R A (ε (a i))
  have hDt : ∀ i, D R A (t i) = D R A (a i) := by intro i; simp [t]
  have hεt : ∀ i, ε (t i) = 0 := by intro i; simp [t]
  let e : (κ →₀ A) →ₗ[A] Ω[A⁄R] :=
    Finsupp.linearCombination A fun i : κ ↦ D R A (t i)
  let l₁ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime p))
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[Localization.AtPrime p⁄R] := map R R A (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, hDt]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A _)
  let l₂ₜ : Ω[A⁄R] →ₗ[A] Ω[Localization.Away g⁄R] :=
    map R R A (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  let bB : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hbB : ∀ i, bB i = D R _ (algebraMap A (Localization.Away g) (t i)) := by
    intro i
    have h1 : bB i = eₜ' (Finsupp.single i 1) := by
      rfl
    rw [h1]
    trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e <| l₁ₜ <| Finsupp.single i 1
    · simp [eₜ', -IsLocalizedModule.map_apply, l₁ₜ]
    · simp [l₂ₜ, e]
  let eκ : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  refine ⟨Nat.card κ, t ∘ eκ.symm, g, fun i => hεt _, ?_, ?_⟩
  · have hg' : ε g ∉ maximalIdeal R := hg
    exact (IsLocalRing.notMem_maximalIdeal.mp hg')
  · unfold EtChart
    letI inst : Algebra (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      ((algebraMap A (Localization.Away g)).comp (MvPolynomial.aeval (t ∘ eκ.symm)).toRingHom).toAlgebra
    show Algebra.Etale (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g)
    have hsc : IsScalarTower R (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R (Localization.Away g) r =
          algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
    have hX : ∀ i, algebraMap (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) (MvPolynomial.X i) =
        algebraMap A (Localization.Away g) (t (eκ.symm i)) := by
      intro i
      change algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X]; rfl
    haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
    haveI : Algebra.FormallySmooth R (Localization.Away g) := Algebra.FormallySmooth.comp R A (Localization.Away g)
    let P := MvPolynomial (Fin (Nat.card κ)) R
    let bP : Module.Basis (Fin (Nat.card κ)) (Localization.Away g) ((Localization.Away g) ⊗[P] Ω[P⁄R]) :=
      (mvPolynomialBasis R (Fin (Nat.card κ))).baseChange (Localization.Away g)
    let bB' := bB.reindex eκ
    have hbij : Function.Bijective (mapBaseChange R P (Localization.Away g)) := by
      have : mapBaseChange R P (Localization.Away g) = (bP.equiv bB' (Equiv.refl _)).toLinearMap := by
        refine bP.ext fun i => ?_
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        simp [bP, bB', hbB, ← hX, P]
      rw [this]
      exact (bP.equiv bB' (Equiv.refl _)).bijective
    haveI : Algebra.FormallyEtale P (Localization.Away g) :=
      formallyEtale_of_bijective_kaehler_mapBaseChange R P (Localization.Away g) hbij
    haveI : Algebra.FinitePresentation R (Localization.Away g) :=
      Algebra.FinitePresentation.trans R A (Localization.Away g)
    haveI : Algebra.FinitePresentation P (Localization.Away g) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P (Localization.Away g)
    exact ⟨inferInstance, inferInstance⟩
end GlobalTheory.DenseSec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleChartSmoothAlgebraLocalPointStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  first | exact @GlobalTheory.DenseSec.exists_etChart | exact GlobalTheory.DenseSec.exists_etChart | (intros; apply GlobalTheory.DenseSec.exists_etChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftingResidueValues

section

section

open IsLocalRing

namespace GlobalTheory.DenseSec

theorem factorₐ_comp_factorₐ {P R : Type} [CommRing P] [CommRing R] [Algebra P R] {I J K : Ideal R}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    (Ideal.Quotient.factorₐ P hJK).comp (Ideal.Quotient.factorₐ P hIJ) =
      Ideal.Quotient.factorₐ P (hIJ.trans hJK) := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem hensel_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R →
    ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h →
    ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) →
    ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  intro R _ _ hc A _ _ g t h hE ε hε c hcε
  classical
  haveI := hc
  letI iPB : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI iPR : Algebra (MvPolynomial (Fin g) R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  have hPB : ∀ p, algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p =
      algebraMap A (Localization.Away h) (MvPolynomial.aeval t p) := fun _ => rfl
  have hPR : ∀ p, algebraMap (MvPolynomial (Fin g) R) R p = MvPolynomial.aeval c p := fun _ => rfl
  let m := maximalIdeal R

  let e' : Localization.Away h →+* R := IsLocalization.Away.lift h (g := (ε : A →+* R)) hε
  have he' : ∀ x : A, e' (algebraMap A (Localization.Away h) x) = ε x := fun x =>
    IsLocalization.Away.lift_eq h (g := (ε : A →+* R)) hε x
  have hmod : (Ideal.Quotient.mk m).comp ((ε : A →+* R).comp (MvPolynomial.aeval (R := R) t).toRingHom) =
      (Ideal.Quotient.mk m).comp (MvPolynomial.aeval c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact (Ideal.Quotient.eq.2 (by
        have := hcε i
        rw [← neg_mem_iff, neg_sub] at this
        exact this))
  let f₁ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m :=
    { toRingHom := (Ideal.Quotient.mk m).comp e'
      commutes' := fun p => by
        show Ideal.Quotient.mk m (e' (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p)) =
          algebraMap (MvPolynomial (Fin g) R) (R ⧸ m) p
        rw [hPB, he']
        show Ideal.Quotient.mk m (ε (MvPolynomial.aeval t p)) = Ideal.Quotient.mk m (MvPolynomial.aeval c p)
        exact congrArg (fun φ : MvPolynomial (Fin g) R →+* R ⧸ m => φ p) hmod }

  have hle : ∀ n : ℕ, m ^ (n + 1) ≤ m := fun n => Ideal.pow_le_self n.succ_ne_zero
  let q : ∀ n : ℕ, R ⧸ m ^ (n + 1) →ₐ[MvPolynomial (Fin g) R] R ⧸ m := fun n =>
    Ideal.Quotient.factorₐ _ (hle n)
  have hqs : ∀ n, Function.Surjective (q n) := fun n x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hqn : ∀ n, IsNilpotent (RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m)) := fun n => by
    refine ⟨n + 1, le_bot_iff.1 ?_⟩
    have hk : RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m) = Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m :=
      Ideal.Quotient.factor_ker (hle n)
    rw [hk, ← Ideal.map_pow, Ideal.map_quotient_self]
  let F : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ (n + 1) := fun n =>
    Algebra.FormallySmooth.liftOfSurjective f₁ (q n) (hqs n) (hqn n)
  have hF : ∀ n, (q n).comp (F n) = f₁ := fun n => Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hFc : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn))).comp (F n) = F k := by
    intro k n hkn
    refine Algebra.FormallyUnramified.ext' (q k : R ⧸ m ^ (k + 1) →+* R ⧸ m) (hqn k) _ _ fun x => ?_
    have h1 := congrArg (fun φ => φ x) (hF n)
    have h2 := congrArg (fun φ => φ x) (hF k)
    simp only [AlgHom.comp_apply] at h1 h2
    show (q k) ((Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1))) (F n x)) = q k (F k x)
    rw [h2, ← h1]
    have := congrArg (fun φ => φ (F n x)) (factorₐ_comp_factorₐ (P := MvPolynomial (Fin g) R)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1)) (hle k))
    simpa only [AlgHom.comp_apply] using this
  let f : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ n := fun n =>
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (F n)
  have hf : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right hkn)).comp (f n) = f k := by
    intro k n hkn
    simp only [f]
    rw [← AlgHom.comp_assoc, factorₐ_comp_factorₐ, ← hFc hkn, ← AlgHom.comp_assoc, factorₐ_comp_factorₐ]
  let Φ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R := IsAdicComplete.liftAlgHom m f hf
  let a : A →ₐ[R] R :=
    { toRingHom := (Φ : Localization.Away h →+* R).comp (algebraMap A (Localization.Away h))
      commutes' := fun r => by
        show Φ (algebraMap A (Localization.Away h) (algebraMap R A r)) = algebraMap R R r
        have : algebraMap A (Localization.Away h) (algebraMap R A r) =
            algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.C r) := by
          rw [hPB, MvPolynomial.aeval_C]
        rw [this, Φ.commutes, hPR, MvPolynomial.aeval_C] }
  refine ⟨a, ?_, fun i => ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit h).map Φ
  · show Φ (algebraMap A (Localization.Away h) (t i)) = c i
    have : algebraMap A (Localization.Away h) (t i) =
        algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.X i) := by
      rw [hPB, MvPolynomial.aeval_X]
    rw [this, Φ.commutes, hPR, MvPolynomial.aeval_X]

end GlobalTheory.DenseSec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftingResidueValuesStatement

section

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_section_lifting_residue_values : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  first | exact @GlobalTheory.DenseSec.hensel_etChart | exact GlobalTheory.DenseSec.hensel_etChart | (intros; apply GlobalTheory.DenseSec.hensel_etChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibres

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DenseSec
theorem chart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point
theorem hensel : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := GlobalTheory.T.exists_section_lifting_residue_values
theorem fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := GlobalTheory.T.exists_poly_vanishing_of_fiber
theorem reduce : (∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := GlobalTheory.T.denseSections_of_algebraic_affineNbhd

theorem image_maximalIdeal_infinite {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hker : RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R) :
    (algebraMap R Ω '' (maximalIdeal R : Set R)).Infinite := by
  have hle : RingHom.ker (algebraMap R Ω) ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨m0, hm0, hm0k⟩ : ∃ m0 ∈ maximalIdeal R, m0 ∉ RingHom.ker (algebraMap R Ω) := by
    by_contra hcon
    push_neg at hcon
    exact hker (le_antisymm hle hcon)
  rw [RingHom.mem_ker] at hm0k
  have hne : ∀ n k : ℕ, n < k → algebraMap R Ω (m0 ^ (n + 1)) ≠ algebraMap R Ω (m0 ^ (k + 1)) := by
    intro n k hnk heq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hnk
    have h1 : algebraMap R Ω (m0 ^ (d + 1)) = 1 := by
      have hpow : algebraMap R Ω (m0 ^ (n + 1)) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hm0k
      have : algebraMap R Ω (m0 ^ (n + 1)) * algebraMap R Ω (m0 ^ (d + 1)) = algebraMap R Ω (m0 ^ (n + 1)) * 1 := by
        rw [_root_.mul_one, ← map_mul, ← _root_.pow_add, heq]
        congr 2
        omega
      exact mul_left_cancel₀ hpow this
    have h2 : 1 - m0 ^ (d + 1) ∈ maximalIdeal R :=
      hle (by rw [RingHom.mem_ker, map_sub, map_one, h1, sub_self])
    have h3 : m0 ^ (d + 1) ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ hm0 _ d.succ_pos
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.add_mem _ h2 h3))
  have hinj : Function.Injective (fun n : ℕ => algebraMap R Ω (m0 ^ (n + 1))) := by
    intro n k h
    by_contra hnk
    rcases lt_or_gt_of_ne hnk with hlt | hlt
    · exact hne n k hlt h
    · exact hne k n hlt h.symm
  exact Set.infinite_of_injective_forall_mem hinj (fun n => ⟨m0 ^ (n + 1), Ideal.pow_mem_of_mem _ hm0 _ n.succ_pos, rfl⟩)

theorem exists_eval_ne_zero_of_infinite {Ω : Type} [Field Ω] (S : Set Ω) (hS : S.Infinite) (g : ℕ)
    (Q : MvPolynomial (Fin g) Ω) (hQ : Q ≠ 0) : ∃ c : Fin g → Ω, (∀ i, c i ∈ S) ∧ MvPolynomial.eval c Q ≠ 0 := by
  obtain ⟨T, hTS, hT⟩ := hS.exists_subset_card_eq (Q.totalDegree + 1)
  by_contra hcon
  push_neg at hcon
  apply hQ
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ => T) (fun i => ?_) (fun x hx => hcon x (fun i => hTS (hx i)))
  rw [hT]
  exact Nat.lt_succ_of_le (MvPolynomial.degreeOf_le_totalDegree Q i)

theorem key : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0 := by
  intro R _ _ hc A _ _ _ ε Ω _ _ hker hirr f hf
  obtain ⟨g, t, h, ht0, hεh, hch⟩ := chart R A ε
  obtain ⟨Q, hQ, hQv⟩ := fibre R A g t h hch Ω hirr f hf
  obtain ⟨c', hc'S, hc'Q⟩ := exists_eval_ne_zero_of_infinite _ (image_maximalIdeal_infinite hker) g Q hQ
  choose c hcm hcc using hc'S
  obtain ⟨a, hah, hat⟩ := hensel R hc A g t h hch ε hεh c (fun i => by simpa [ht0] using hcm i)
  refine ⟨a, fun h0 => hc'Q ?_⟩
  have hv := hQv ((Algebra.ofId R Ω).comp a) (by simpa using (hah.map (algebraMap R Ω)).ne_zero) h0
  have hc' : c' = fun i => ((Algebra.ofId R Ω).comp a) (t i) := by
    funext i
    simp [hat, hcc]
  rw [hc']
  exact hv

theorem dense_sections : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := reduce key
end GlobalTheory.DenseSec
end
end
end
