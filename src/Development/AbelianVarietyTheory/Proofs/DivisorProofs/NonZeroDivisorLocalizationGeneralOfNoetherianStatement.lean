module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreGoingDownTensor

section

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem fibre_going_down_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  intro S A C _ _ _ _ _ u _ Q₁ _ hle h2
  let p := u.comap (algebraMap A (A ⊗[S] C))
  let p₁ := u.comap (algebraMap S (A ⊗[S] C))
  have hp : p₁ = p.comap (algebraMap S A) := by
    simp only [p, p₁, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  let K₁ := p₁.ResidueField
  let K := p.ResidueField
  letI : Algebra K₁ K := (Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).toAlgebra
  haveI : IsScalarTower S K₁ K := IsScalarTower.of_algebraMap_eq
    (fun s => ((Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).commutes s).symm)
  let F₁ := p₁.Fiber C
  let E := F₁ ⊗[K₁] K
  let e1 : p.Fiber (A ⊗[S] C) ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S A K K C
  let e2 : K ⊗[K₁] F₁ ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S K₁ K K C
  let e3 : K ⊗[K₁] F₁ ≃ₐ[K₁] E := Algebra.TensorProduct.comm K₁ K F₁
  haveI : Module.Flat F₁ E := inferInstance
  haveI : Algebra.HasGoingDown F₁ E := inferInstance
  let Φ : p.Fiber (A ⊗[S] C) ≃+* E :=
    (e1.toRingEquiv.trans e2.symm.toRingEquiv).trans e3.toRingEquiv
  have hΦ : ∀ c : C, Φ (Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight c : A ⊗[S] C))
      = algebraMap F₁ E (Algebra.TensorProduct.includeRight c) := by
    intro c
    simp only [Φ, e1, e2, e3, Algebra.TensorProduct.includeRight_apply, RingEquiv.trans_apply,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    erw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    rfl

  haveI : u.LiesOver p := ⟨rfl⟩
  let isoA := PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗[S] C) p
  let ub := isoA ⟨u, inferInstance, inferInstance⟩
  have hub : ub.asIdeal.comap (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) = u := by
    have := congrArg Subtype.val (isoA.symm_apply_apply ⟨u, inferInstance, inferInstance⟩)
    exact this
  have hmem : ∀ y : A ⊗[S] C, (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) y
      ∈ ub.asIdeal ↔ y ∈ u := fun y => Iff.of_eq (congrArg (y ∈ ·) hub)

  haveI : Q₁.LiesOver p₁ := ⟨h2.symm⟩
  let iso₁ := PrimeSpectrum.primesOverOrderIsoFiber S C p₁
  let Qb := iso₁ ⟨Q₁, inferInstance, inferInstance⟩
  have hQb : Qb.asIdeal.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) = Q₁ := by
    have := congrArg Subtype.val (iso₁.symm_apply_apply ⟨Q₁, inferInstance, inferInstance⟩)
    exact this

  let ue : Ideal E := ub.asIdeal.comap (Φ.symm : E →+* p.Fiber (A ⊗[S] C))
  haveI : ue.IsPrime := Ideal.comap_isPrime _ _
  let w : Ideal F₁ := ue.comap (algebraMap F₁ E)
  haveI : w.IsPrime := Ideal.comap_isPrime _ _
  haveI : ue.LiesOver w := ⟨rfl⟩
  have hw : w.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) =
      u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C) := by
    ext c
    change Φ.symm (algebraMap F₁ E (Algebra.TensorProduct.includeRight c)) ∈ ub.asIdeal ↔ _
    rw [← hΦ, RingEquiv.symm_apply_apply]
    exact hmem _
  have hwle : Qb.asIdeal ≤ w := by
    let u₁ := u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C)
    haveI : u₁.IsPrime := Ideal.comap_isPrime _ _
    haveI : u₁.LiesOver p₁ := ⟨by
      show p₁ = u₁.comap (algebraMap S C)
      ext s
      simp [u₁, p₁]⟩
    let wP : PrimeSpectrum F₁ := ⟨w, inferInstance⟩
    have hsym : (iso₁.symm wP).1 = u₁ := hw
    have key : iso₁.symm Qb ≤ iso₁.symm wP := by
      show (iso₁.symm Qb).1 ≤ (iso₁.symm wP).1
      rw [hsym, iso₁.symm_apply_apply]
      exact hle
    exact (iso₁.symm.le_iff_le.mp key : Qb ≤ wP)
  obtain ⟨P, hPle, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Qb.asIdeal) (q := w) ue hwle
  refine ⟨(P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap
    (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)), inferInstance, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hmem]
    have := hPle hx
    simpa [ue] using this
  · ext c
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
    erw [hΦ c]
    rw [← hQb, Ideal.mem_comap, ← Ideal.mem_comap, ← Ideal.under_def, ← hPover.over]
  · ext a
    let J : Ideal K := (P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap (algebraMap K (p.Fiber (A ⊗[S] C)))
    haveI : J.IsPrime := Ideal.comap_isPrime _ _
    have hJ : J = ⊥ := Ideal.eq_bot_of_prime J
    have hx : (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C))
        (algebraMap A (A ⊗[S] C) a) = algebraMap K (p.Fiber (A ⊗[S] C)) (algebraMap A K a) := by
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    rw [Ideal.mem_comap, Ideal.mem_comap, hx]
    change algebraMap A K a ∈ J ↔ _
    rw [hJ, Ideal.mem_bot, Ideal.algebraMap_residueField_eq_zero]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreGoingDownTensorStatement

section

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_prime_le_comap_of_goingDown_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  first | exact @GlobalTheory.fibre_going_down_tensor | exact GlobalTheory.fibre_going_down_tensor | (intros; apply GlobalTheory.fibre_going_down_tensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonZeroDivisorLocalizationGeneralOfNoetherian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NzdDescent

open TensorProduct GlobalTheory.SmoothDescent

theorem model_data (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b g : B) :
    ∃ (S B₁ : Type) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : Algebra S A) (_ : CommRing B₁)
      (_ : Algebra S B₁) (_ : Algebra.Smooth S B₁) (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁),
      Function.Injective (fun x : B₁ => e (1 ⊗ₜ x)) ∧ e (1 ⊗ₜ b₁) = b ∧ e (1 ⊗ₜ g₁) = g := by
  classical
  obtain ⟨A₀, B₀, _, _, h₀, hB, ⟨β⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  haveI : IsNoetherianRing A₀ := isNoetherianRing_of_fg h₀
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := B₀) ({β b, β g} : Finset _)
  obtain ⟨b₁, hb₁⟩ := hsub (by simp : β b ∈ _)
  obtain ⟨g₁, hg₁⟩ := hsub (by simp : β g ∈ _)
  set_option synthInstance.maxHeartbeats 200000 in
   refine ⟨S, S ⊗[A₀] B₀, inferInstance, isNoetherianRing_of_fg hS, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (Algebra.TensorProduct.cancelBaseChange A₀ S A A B₀).trans β.symm, b₁, g₁, ?_, ?_, ?_⟩
  · intro x y h
    simp only [AlgEquiv.trans_apply, cancel_one_tmul] at h
    exact incl_injective S (β.symm.injective h)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hb₁).trans (β.symm_apply_apply b)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hg₁).trans (β.symm_apply_apply g)

theorem of_model (hN : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0)) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (S B₁ : Type) (b g : B) [CommRing S] [IsNoetherianRing S] [Algebra S A] [CommRing B₁] [Algebra S B₁]
    [Algebra.Smooth S B₁] (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁)
    (hinj : Function.Injective (fun x : B₁ => e (1 ⊗ₜ x))) (hb : e (1 ⊗ₜ b₁) = b) (hg : e (1 ⊗ₜ g₁) = g)
    (u : PrimeSpectrum B) (hgb : g * b = 0)
    (hmin : ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q) :
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  let ι : B₁ →+* B := e.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).toRingHom
  have hι : ∀ x, ι x = e (1 ⊗ₜ x) := fun x => rfl
  have hιS : ∀ s : S, ι (algebraMap S B₁ s) = algebraMap A B (algebraMap S A s) := by
    intro s
    rw [hι, ← Algebra.TensorProduct.tmul_one_eq_one_tmul, ← Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.algebraMap_apply S A (A ⊗[S] B₁), AlgEquiv.commutes]
  have hgb₁ : g₁ * b₁ = 0 := by
    apply hinj
    show ι (g₁ * b₁) = ι 0
    rw [map_mul, hι, hι, hg, hb, hgb, map_zero]
  let u₁ : PrimeSpectrum B₁ := ⟨u.asIdeal.comap ι, Ideal.comap_isPrime _ _⟩
  have key := hN S B₁ b₁ g₁ u₁ hgb₁ ?_
  · obtain ⟨⟨t, ht⟩, htb⟩ := (IsLocalization.map_eq_zero_iff u₁.asIdeal.primeCompl _ b₁).mp key
    refine (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).mpr ⟨⟨ι t, ht⟩, ?_⟩
    show ι t * b = 0
    rw [← hb, ← hι, ← map_mul]
    simp only at htb
    rw [htb, map_zero]
  intro Q₁ hQ₁ hQ₁u hgQ₁
  haveI : Q₁.IsPrime := hQ₁.1.1
  let uT : Ideal (A ⊗[S] B₁) := u.asIdeal.comap e.toAlgHom.toRingHom
  haveI : uT.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨QT, hQTp, hQTu, hQT1, hQTA⟩ := GlobalTheory.T.exists_prime_le_comap_of_goingDown_tensor S A B₁ uT Q₁ (fun x hx => hQ₁u hx) (by
    apply le_antisymm
    · intro s hs
      have : algebraMap S B₁ s ∈ u₁.asIdeal := hQ₁u hs
      show e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal
      rw [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes]
      exact this
    · intro s hs
      apply hQ₁.1.2
      apply Ideal.mem_map_of_mem
      show ι (algebraMap S B₁ s) ∈ u.asIdeal
      have : e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal := hs
      rwa [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes] at this)
  let Q' : Ideal B := QT.comap e.symm.toAlgHom.toRingHom
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hQ'u : Q' ≤ u.asIdeal := by
    intro x hx
    have := hQTu hx
    simpa [uT] using this
  have hmap : (u.asIdeal.comap (algebraMap A B)).map (algebraMap A B) ≤ Q' := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have h1 : a ∈ uT.comap (algebraMap A (A ⊗[S] B₁)) := by
      show e (algebraMap A _ a) ∈ u.asIdeal
      rw [AlgEquiv.commutes]; exact ha
    rw [← hQTA] at h1
    show e.symm (algebraMap A B a) ∈ QT
    rw [AlgEquiv.commutes]; exact h1
  obtain ⟨Q, hQmin, hQQ'⟩ := Ideal.exists_minimalPrimes_le hmap
  apply hmin Q hQmin (hQQ'.trans hQ'u)
  haveI : Q.IsPrime := hQmin.1.1
  have hJ : Q₁ ≤ Q.comap ι := by
    refine hQ₁.2 ⟨Ideal.comap_isPrime _ _, ?_⟩ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      show ι (algebraMap S B₁ s) ∈ Q
      rw [hιS]
      apply hQmin.1.2
      apply Ideal.mem_map_of_mem
      show algebraMap A B (algebraMap S A s) ∈ u.asIdeal
      rw [← hιS]; exact hs
    · intro x hx
      rw [← hQT1]
      have := hQQ' hx
      have h2 : e.symm (e (1 ⊗ₜ x)) ∈ QT := this
      rw [AlgEquiv.symm_apply_apply] at h2
      exact h2
  have := hJ hgQ₁
  rw [← hg]; exact this

theorem of_noetherian : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro hN A B _ _ _ _ b g u hgb hmin
  obtain ⟨S, B₁, _, _, _, _, _, _, e, b₁, g₁, hinj, hb, hg⟩ := model_data A B b g
  exact of_model hN A B S B₁ b g e b₁ g₁ hinj hb hg u hgb hmin

end GlobalTheory.NzdDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonZeroDivisorLocalizationGeneralOfNoetherianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.nonZeroDivisor_localization_general_of_noetherian : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  first | exact @GlobalTheory.NzdDescent.of_noetherian | exact GlobalTheory.NzdDescent.of_noetherian | (intros; apply GlobalTheory.NzdDescent.of_noetherian <;> assumption)
end
end
