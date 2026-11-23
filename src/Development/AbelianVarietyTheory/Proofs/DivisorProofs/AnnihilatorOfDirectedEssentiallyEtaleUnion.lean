module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumDen

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory
namespace SpreadOut

lemma exists_num_den {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime]
    (y : Localization.AtPrime p) :
    ∃ a s : T, s ∉ p ∧ algebraMap T _ s * y = algebraMap T _ a := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  exact ⟨a, s, s.2, IsLocalization.mk'_spec' _ a s⟩

lemma prod_not_mem {T : Type} [CommRing T] {ι : Type} (p : Ideal T) [p.IsPrime]
    (S : Finset ι) (g : ι → T) (h : ∀ i ∈ S, g i ∉ p) : ∏ i ∈ S, g i ∉ p :=
  Submonoid.prod_mem p.primeCompl (fun i hi => h i hi)

lemma exists_kill {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime] (f₀ : T)
    (z : Localization.Away f₀)
    (ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p) (hz : ι₀ z = 0) :
    ∃ t : T, t ∉ p ∧ ∀ (B : Type) [CommRing B] [Algebra T B]
      (κ : Localization.Away f₀ →ₐ[T] B), IsUnit (algebraMap T B t) → κ z = 0 := by
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f₀) z
  have hspec := IsLocalization.mk'_spec' (Localization.Away f₀) b m
  have h1 : algebraMap T (Localization.AtPrime p) b = 0 := by
    have := congrArg ι₀ hspec
    rw [map_mul, AlgHom.commutes, AlgHom.commutes, hz, mul_zero] at this
    exact this.symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ b).1 h1
  refine ⟨t, t.2, fun B _ _ κ hu => ?_⟩
  have h2 := congrArg κ hspec
  rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h2
  have hb : algebraMap T B b = 0 := by
    apply hu.mul_left_cancel
    rw [← map_mul, ht, map_zero, mul_zero]
  have hm : IsUnit (algebraMap T B m) := by
    rw [← AlgHom.commutes κ]
    exact (IsLocalization.map_units (Localization.Away f₀) m).map κ
  rw [hb] at h2
  exact hm.mul_right_eq_zero.1 h2

theorem spread_out : ∀ (T A : Type) [CommRing T] [CommRing A] [Algebra T A]
    [Algebra.FinitePresentation T A] (p : Ideal T) [p.IsPrime]
    (φ : A →ₐ[T] Localization.AtPrime p), ∃ f : T, f ∉ p ∧
      ∃ (s : A →ₐ[T] Localization.Away f) (ι : Localization.Away f →ₐ[T] Localization.AtPrime p),
        ι.comp s = φ := by
  intro T A _ _ _ _ p _ φ
  obtain ⟨n, π, hπ, hker⟩ := Algebra.FinitePresentation.out (R := T) (A := A)
  obtain ⟨G, hG⟩ := hker
  choose a s hs hy using fun i : Fin n => exists_num_den p (φ (π (MvPolynomial.X i)))
  set f₀ : T := ∏ i, s i with hf₀
  have hf₀p : f₀ ∉ p := prod_not_mem p _ s (fun i _ => hs i)
  have hu₀ : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f₀) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f₀, hf₀p⟩ : p.primeCompl)
  let ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ hu₀
  have hu : ∀ i, IsUnit (algebraMap T (Localization.Away f₀) (s i)) := fun i =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem s (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit f₀)
  let x : Fin n → Localization.Away f₀ := fun i =>
    algebraMap T _ (a i) * ↑(hu i).unit⁻¹
  let ψ₀ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f₀ := MvPolynomial.aeval x
  have hι0 : ∀ i, ι₀ (x i) = φ (π (MvPolynomial.X i)) := by
    intro i
    have hu' : IsUnit (algebraMap T (Localization.AtPrime p) (s i)) :=
      IsLocalization.map_units _ (⟨s i, hs i⟩ : p.primeCompl)
    apply hu'.mul_left_cancel
    rw [hy i, ← AlgHom.commutes ι₀ (s i), ← map_mul]
    simp only [x]
    rw [mul_left_comm, IsUnit.mul_val_inv, mul_one, AlgHom.commutes]
  have hφ : ι₀.comp ψ₀ = φ.comp π := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, ψ₀, MvPolynomial.aeval_X]
    exact hι0 i
  have hzero : ∀ g : G, ι₀ (ψ₀ g) = 0 := by
    intro g
    have hg : (g : MvPolynomial (Fin n) T) ∈ RingHom.ker π.toRingHom := by
      rw [← hG]; exact Ideal.subset_span g.2
    rw [RingHom.mem_ker] at hg
    have := congrArg (fun h => h (g : MvPolynomial (Fin n) T)) hφ
    simp only [AlgHom.comp_apply] at this
    rw [this]
    have hg' : π g = 0 := hg
    rw [hg', map_zero]
  choose t ht hkill using fun g : G => exists_kill p f₀ (ψ₀ g) ι₀ (hzero g)
  set f : T := f₀ * ∏ g, t g with hfdef
  have hfp : f ∉ p :=
    p.primeCompl.mul_mem hf₀p (prod_not_mem p _ t (fun g _ => ht g))
  have huj : IsUnit ((Algebra.ofId T (Localization.Away f)) f₀) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f₀ _)) (IsLocalization.Away.algebraMap_isUnit f)
  let j : Localization.Away f₀ →ₐ[T] Localization.Away f :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ huj
  let ψ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f := j.comp ψ₀
  have hψG : ∀ g : G, ψ g = 0 := by
    intro g
    apply hkill g (Localization.Away f) j
    exact isUnit_of_dvd_unit
      (map_dvd _ (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem t (Finset.mem_univ g)) f₀))
      (IsLocalization.Away.algebraMap_isUnit f)
  have hspan : Ideal.span (G : Set (MvPolynomial (Fin n) T)) ≤
      RingHom.ker (ψ : MvPolynomial (Fin n) T →+* Localization.Away f) := by
    rw [Ideal.span_le]
    intro g hg
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact hψG ⟨g, hg⟩
  have hψker : ∀ q : MvPolynomial (Fin n) T, q ∈ RingHom.ker π → ψ q = 0 := by
    intro q hq
    have hq' : q ∈ Ideal.span (G : Set (MvPolynomial (Fin n) T)) := by
      rw [hG]; exact hq
    exact (RingHom.mem_ker).1 (hspan hq')
  let sq := Ideal.Quotient.liftₐ (RingHom.ker π) ψ hψker
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let σ : A →ₐ[T] Localization.Away f := sq.comp e.symm.toAlgHom
  have hσ : ∀ q, σ (π q) = ψ q := by
    intro q
    have : e.symm (π q) = Ideal.Quotient.mk (RingHom.ker π) q := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show sq (e.symm (π q)) = ψ q
    rw [this]
    simp only [sq, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  have huι : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f, hfp⟩ : p.primeCompl)
  let ι : Localization.Away f →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f) f huι
  refine ⟨f, hfp, σ, ι, ?_⟩
  have hιj : ι.comp j = ι₀ :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers f₀)).elim _ _
  apply AlgHom.ext
  intro y
  obtain ⟨q, rfl⟩ := hπ y
  rw [AlgHom.comp_apply, hσ q]
  have h1 := congrArg (fun h => h (ψ₀ q)) hιj
  have h2 := congrArg (fun h => h q) hφ
  simp only [AlgHom.comp_apply] at h1 h2
  simp only [ψ, AlgHom.comp_apply]
  rw [h1, h2]

end SpreadOut
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLocalizationAtPrimeFactorsThroughAway

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory
namespace FactorAway

theorem factor_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime]
    (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p)
      (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift
        (algebraMap B (Localization.AtPrime p)) g
        (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  intro R A B _ _ _ _ _ _ p _ φ
  let φ' : B ⊗[R] A →ₐ[B] Localization.AtPrime p :=
    Algebra.TensorProduct.lift (Algebra.ofId B _) φ (fun _ _ => Commute.all _ _)
  obtain ⟨g, hg, s, ι, hι⟩ := SpreadOut.spread_out B (B ⊗[R] A) p φ'
  refine ⟨g, hg, (s.restrictScalars R).comp Algebra.TensorProduct.includeRight, fun a => ?_⟩
  have hext : (Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
      (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl))) =
      (ι : Localization.Away g →+* Localization.AtPrime p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext b
    simp [Localization.awayLift]
  have h1 := congrArg (fun h => h ((1 : B) ⊗ₜ[R] a)) hι
  simp only [AlgHom.comp_apply, φ', Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h1
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
  rw [hext]
  exact h1

end FactorAway
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLocalizationAtPrimeFactorsThroughAwayStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.algHom_localizationAtPrime_factors_through_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p) (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift (algebraMap B (Localization.AtPrime p)) g (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  first | exact @GlobalTheory.FactorAway.factor_away | exact GlobalTheory.FactorAway.factor_away | (intros; apply GlobalTheory.FactorAway.factor_away <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfEssentiallyEtaleLocalAlgebras

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem flat_of_algHom_atPrime (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Algebra.Etale R B] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p) :
    φ.toRingHom.Flat := by
  obtain ⟨g, hg, ψ, hψ⟩ := GlobalTheory.T.algHom_localizationAtPrime_factors_through_away R A B p φ
  set h := Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
    (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) with hh
  have e : φ.toRingHom = h.comp ψ.toRingHom := by ext a; exact (hψ a).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · letI : Algebra A (Localization.Away g) := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower R A (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
    haveI : Algebra.Etale A (Localization.Away g) := Algebra.Etale.of_restrictScalars R A _
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · letI : Algebra (Localization.Away g) (Localization.AtPrime p) := h.toAlgebra
    haveI : IsScalarTower B (Localization.Away g) (Localization.AtPrime p) :=
      IsScalarTower.of_algebraMap_eq (fun b => by
        change _ = h _
        simp [hh, Localization.awayLift, IsLocalization.Away.lift])
    have : Module.Flat (Localization.Away g) (Localization.AtPrime p) :=
      (Module.flat_iff_of_isLocalization (Localization.Away g) (Submonoid.powers g)
        (Localization.AtPrime p)).mpr inferInstance
    exact RingHom.flat_algebraMap_iff.mpr this

theorem flat_of_essEtale : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  intro R L₁ L₂ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨e₁⟩⟩ ⟨A', _, _, _, q', _, ⟨e₂⟩⟩
  let φ : A →ₐ[R] Localization.AtPrime q' :=
    (e₂.symm.toAlgHom.comp (IsScalarTower.toAlgHom R L₁ L₂)).comp
      (e₁.toAlgHom.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)))
  have hφ := flat_of_algHom_atPrime R A A' q' φ
  let f : A →+* L₁ := e₁.toRingHom.comp (algebraMap A (Localization.AtPrime q))
  letI : Algebra A L₁ := f.toAlgebra
  letI : Algebra A L₂ := ((algebraMap L₁ L₂).comp f).toAlgebra
  haveI : IsScalarTower A L₁ L₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁' : Localization.AtPrime q ≃ₐ[A] L₁ := { e₁ with commutes' := fun _ => rfl }
  haveI : IsLocalization q.primeCompl L₁ := IsLocalization.isLocalization_of_algEquiv q.primeCompl e₁'
  have hflat : Module.Flat A L₂ := by
    rw [← RingHom.flat_algebraMap_iff]
    have : algebraMap A L₂ = e₂.toRingHom.comp φ.toRingHom := by
      ext a; simp [φ, f, RingHom.algebraMap_toAlgebra]
    rw [this]
    exact RingHom.Flat.comp hφ (RingHom.Flat.of_bijective e₂.bijective)
  exact (Module.flat_iff_of_isLocalization L₁ q.primeCompl L₂).mpr hflat

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfEssentiallyEtaleLocalAlgebrasStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.flat_of_essentiallyEtale_local_algebras : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  first | exact @GlobalTheory.flat_of_essEtale | exact GlobalTheory.flat_of_essEtale | (intros; apply GlobalTheory.flat_of_essEtale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfDirectedEssentiallyEtaleUnion

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 400000 in
theorem ann_of_directed_essEtale : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → ∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0 := by
  intro R B _ _ _ Q _ ι _ _ C hmono hcov hess i c hc t ht htc
  obtain ⟨j, hj⟩ := hcov t
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hck : c ∈ C k := hmono hik hc
  have htk : t ∈ C k := hmono hjk hj
  set Qi := Q.comap ((C i).val : C i →ₐ[R] B) with hQi
  set Qk := Q.comap ((C k).val : C k →ₐ[R] B) with hQk
  let f : C i →+* C k := (Subalgebra.inclusion (hmono hik)).toRingHom
  have hf : Qi = Qk.comap f := by ext x; rfl
  let g : Localization.AtPrime Qi →+* Localization.AtPrime Qk := Localization.localRingHom Qi Qk f hf
  letI : Algebra (Localization.AtPrime Qi) (Localization.AtPrime Qk) := g.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime Qi) (Localization.AtPrime Qk) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change algebraMap R (Localization.AtPrime Qk) r = g (algebraMap R (Localization.AtPrime Qi) r)
    rw [IsScalarTower.algebraMap_apply R (C i) (Localization.AtPrime Qi), IsScalarTower.algebraMap_apply R (C k) (Localization.AtPrime Qk)]
    simp only [g, Localization.localRingHom_to_map]
    congr 1
  haveI : Module.Flat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    GlobalTheory.T.flat_of_essentiallyEtale_local_algebras R _ _ (hess i) (hess k)
  haveI : IsLocalHom (algebraMap (Localization.AtPrime Qi) (Localization.AtPrime Qk)) :=
    (inferInstance : IsLocalHom g)
  haveI : Module.FaithfullyFlat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr this)
  have h0 : algebraMap (C k) (Localization.AtPrime Qk) ⟨c, hck⟩ = 0 := by
    rw [IsLocalization.map_eq_zero_iff Qk.primeCompl]
    refine ⟨⟨⟨t, htk⟩, ht⟩, ?_⟩
    exact Subtype.ext htc
  have h1 : algebraMap (C i) (Localization.AtPrime Qi) ⟨c, hc⟩ = 0 := by
    apply hinj
    rw [map_zero]
    change g _ = 0
    simp only [g, Localization.localRingHom_to_map]
    exact h0
  rw [IsLocalization.map_eq_zero_iff Qi.primeCompl] at h1
  obtain ⟨⟨⟨s, hs⟩, hsQ⟩, hsc⟩ := h1
  exact ⟨s, hs, hsQ, congrArg Subtype.val hsc⟩

end GlobalTheory
end
end
