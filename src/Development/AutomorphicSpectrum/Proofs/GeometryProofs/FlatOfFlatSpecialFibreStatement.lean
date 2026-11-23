module

public import Mathlib.RingTheory.RingHom.Flat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
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
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PfibRing

section

@[expose] public section

open TensorProduct LinearMap IsLocalRing

namespace PositivityTheory.HtPt.Pfib

open GlobalTheory.LocalFlat

theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  apply GlobalTheory.FiniteFibreFlat.lTensor_map_injective <;> assumption

section Devissage

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M]

theorem exists_of_lTensor_eq {F G N : Type} [AddCommGroup F] [Module A F] [AddCommGroup G]
    [Module A G] [AddCommGroup N] [Module A N] (f : F →ₗ[A] N) (g : G →ₗ[A] N)
    (hs : Function.Surjective (f.coprod g)) (x : M ⊗[A] F) (y : M ⊗[A] G)
    (h : f.lTensor M x + g.lTensor M y = 0) :
    ∃ z : M ⊗[A] ker (f.coprod g),
      (fst A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = x ∧
      (snd A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = y := by
  have hex := lTensor_exact M (f.coprod g).exact_subtype_ker_map hs
  have h0 : (f.coprod g).lTensor M ((inl A F G).lTensor M x + (inr A F G).lTensor M y) = 0 := by
    rw [map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply, coprod_inl, coprod_inr, h]
  obtain ⟨z, hz⟩ := (hex _).mp h0
  refine ⟨z, ?_, ?_⟩
  · rw [lTensor_comp_apply, hz, map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply,
      fst_comp_inl, fst_comp_inr]
    simp
  · rw [lTensor_comp_apply, hz, map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply,
      snd_comp_inl, snd_comp_inr]
    simp

theorem lTensor_injective_of_le_range {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) {F : Type} [AddCommGroup F] [Module A F]
    (f : F →ₗ[A] A) (hf : Function.Injective f) (hle : I ≤ range f) :
    Function.Injective (f.lTensor M) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel F f x (by rw [hx]; simp)
  let e₀ : Submodule.comap f I →ₗ[A] I := f.restrict fun _ h => h
  have he : Function.Bijective e₀ := by
    refine ⟨fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨a, ha⟩ := hle i.2
    exact ⟨⟨a, by rw [Submodule.mem_comap, ha]; exact i.2⟩, Subtype.ext ha⟩
  let e := LinearEquiv.ofBijective e₀ he
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← lTensor_comp_apply, ← lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ hI] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem lTensor_injective_of_pow_le [IsNoetherianRing A] {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) (n : ℕ) (J : Ideal A) (hJ : I ^ n ≤ J) :
    Function.Injective (J.subtype.lTensor M) := by
  induction J using WellFoundedGT.induction with
  | ind J ih =>
  by_cases hex : ∃ a, a ∉ J ∧ ∀ i ∈ I, i * a ∈ J
  · obtain ⟨a, ha, hIa⟩ := hex
    let J' : Ideal A := J ⊔ Ideal.span {a}
    have haJ' : a ∈ J' := Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < J' := lt_of_le_of_ne le_sup_left fun h => ha (h ▸ haJ')
    have h' := ih J' hlt (hJ.trans hlt.le)
    let f : J →ₗ[A] J' := Submodule.inclusion hlt.le
    let g : A →ₗ[A] J' := toSpanSingleton A J' ⟨a, haJ'⟩
    have hs : Function.Surjective (f.coprod g) := by
      rintro ⟨b, hb⟩
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      exact ⟨(⟨j, hj⟩, c), rfl⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hfx : f.lTensor M x = 0 := by
      apply h'
      rw [← lTensor_comp_apply, map_zero]
      exact hx
    obtain ⟨z, hz1, hz2⟩ := exists_of_lTensor_eq f g hs x 0 (by rw [hfx, map_zero, add_zero])
    have hinj : Function.Injective
        ((snd A J A ∘ₗ (ker (f.coprod g)).subtype).lTensor M) := by
      refine lTensor_injective_of_le_range hrel hI _ ?_ fun i hi => ?_
      · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        rintro ⟨⟨j, c⟩, hjc⟩ hc
        have hc' : c = 0 := hc
        subst hc'
        have h1 : (j : A) + (0 : A) • a = 0 := congrArg Subtype.val hjc
        have h2 : j = 0 := Subtype.ext (by simpa using h1)
        subst h2
        rfl
      · refine ⟨⟨(⟨-(i * a), neg_mem (hIa i hi)⟩, i), ?_⟩, rfl⟩
        refine Subtype.ext ?_
        change -(i * a) + i • a = 0
        simp
    have hz : z = 0 := hinj (hz2.trans (map_zero _).symm)
    rw [← hz1, hz, map_zero]
  · push Not at hex
    have htop : ∀ m : ℕ, I ^ m ≤ J → (1 : A) ∈ J := by
      intro m
      induction m with
      | zero => intro h; exact h (by simp)
      | succ m ihm =>
        intro h
        refine ihm fun a ha => ?_
        by_contra haJ
        obtain ⟨i, hi, hia⟩ := hex a haJ
        exact hia (h (by rw [pow_succ']; exact Ideal.mul_mem_mul hi ha))
    refine lTensor_injective_of_le_range hrel hI _ J.injective_subtype ?_
    rw [Submodule.range_subtype, (Ideal.eq_top_iff_one J).mpr (htop n hJ)]
    exact le_top

theorem relationsLift_of_injective {J : Ideal A}
    (h : ∀ J' : Ideal A, J ≤ J' → Function.Injective (J'.subtype.lTensor M)) :
    RelationsLift J M := by
  intro F _ _ f x hx
  have hy : ∀ m ∈ J • (⊤ : Submodule A M),
      ∃ y : M ⊗[A] J, TensorProduct.rid A M (J.subtype.lTensor M y) = m := by
    intro m hm
    induction hm using Submodule.smul_induction_on' with
    | smul r hr m _ => exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    | add a _ b _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', by simp⟩
  obtain ⟨y, hy⟩ := hy _ hx
  have hy' := (TensorProduct.rid A M).injective hy
  let J' : Ideal A := range f ⊔ J
  let f' : F →ₗ[A] J' := f.codRestrict J' fun a => Submodule.mem_sup_left ⟨a, rfl⟩
  let g : J →ₗ[A] J' := Submodule.inclusion le_sup_right
  have hs : Function.Surjective (f'.coprod g) := by
    rintro ⟨b, hb⟩
    obtain ⟨_, ⟨a, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
    exact ⟨(a, ⟨c, hc⟩), rfl⟩
  have h0 : f'.lTensor M x + g.lTensor M (-y) = 0 := by
    apply h J' le_sup_right
    rw [map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply, map_zero, map_neg]
    change f.lTensor M x + -(J.subtype.lTensor M y) = 0
    rw [hy', add_neg_cancel]
  obtain ⟨z, hz, -⟩ := exists_of_lTensor_eq f' g hs x (-y) h0
  refine range_lTensor_le _ _ ?_ ⟨z, hz⟩
  rintro ⟨⟨a, j⟩, haj⟩
  have h1 : f a + (j : A) = 0 := congrArg Subtype.val haj
  change f a ∈ J
  rw [eq_neg_of_add_eq_zero_left h1]
  exact neg_mem j.2

theorem flat_of_relationsLift_of_injective [IsNoetherianRing A] (B : Type) [CommRing B]
    [Algebra A B] [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {I : Ideal A} (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (hrel : RelationsLift I M)
    (hinj : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  flat_of_relationsLift B hI fun n =>
    relationsLift_of_injective fun J hJ => lTensor_injective_of_pow_le hrel hinj n J hJ

end Devissage

theorem fibre_crit_ring : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB h
  refine flat_of_relationsLift_of_injective B (I := (maximalIdeal R).map (algebraMap R A)) ?_ ?_
    (lTensor_map_injective _)
  · exact ((Ideal.map_mono (map_maximalIdeal_le _)).trans (map_maximalIdeal_le _)).trans
      (maximalIdeal_le_jacobson _)
  · refine relationsLift_of_square
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A) :
        A →+* ResidueField R ⊗[R] A)
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) :
        B →+* ResidueField R ⊗[R] B) _
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (GlobalTheory.ker_includeRight_quotient A (maximalIdeal R)) ?_ ?_ h
    · rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      exact GlobalTheory.ker_includeRight_quotient B (maximalIdeal R)
    · ext a
      simp

end PositivityTheory.HtPt.Pfib
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleFlatOfFlatAndFibreFlat

section

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  first | exact @PositivityTheory.HtPt.Pfib.fibre_crit_ring | exact PositivityTheory.HtPt.Pfib.fibre_crit_ring
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleFlatOfFlatAndFibreFlatStatement

section

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.module_flat_of_flat_and_fibre_flat : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat | exact GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibre

section

@[expose] public section

open TensorProduct

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem isPushout_cancel (R k A B T U : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [CommRing T] [CommRing U]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra R T] [Algebra R U]
    [Algebra A B] [Algebra A T] [Algebra A U] [Algebra B U] [Algebra k T] [Algebra k U]
    [Algebra T U]
    [IsScalarTower R A B] [IsScalarTower R A T] [IsScalarTower R A U] [IsScalarTower R B U]
    [IsScalarTower R k T] [IsScalarTower R k U] [IsScalarTower k T U] [IsScalarTower A T U]
    [IsScalarTower A B U]
    (h₁ : Algebra.IsPushout R A k T) (h₂ : Algebra.IsPushout R B k U) :
    Algebra.IsPushout A B T U := by
  rw [Algebra.isPushout_iff] at h₁ h₂ ⊢
  refine IsBaseChange.of_comp (R := R) (S := A) (T := B)
    (f := (IsScalarTower.toAlgHom R k T).toLinearMap)
    (h := (IsScalarTower.toAlgHom A T U).toLinearMap) h₁ ?_
  convert h₂ using 1
  ext x
  simp [IsScalarTower.algebraMap_apply k T U]

noncomputable abbrev fibreMap (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    k ⊗[R] A →+* k ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R k) (IsScalarTower.toAlgHom R A B)).toRingHom

theorem fibreMap_isLocalization (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A]
    [CommRing B] [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] :
    letI := (fibreMap R k A B).toAlgebra
    IsLocalization (M.map (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A))
      (k ⊗[R] B) := by
  letI iTU : Algebra (k ⊗[R] A) (k ⊗[R] B) := (fibreMap R k A B).toAlgebra
  letI iAT : Algebra A (k ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  letI iBU : Algebra B (k ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  letI iAU : Algebra A (k ⊗[R] B) := ((algebraMap B (k ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  haveI t1 : IsScalarTower A B (k ⊗[R] B) := .of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower A (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change (1 : k) ⊗ₜ[R] (algebraMap A B a) = fibreMap R k A B ((1 : k) ⊗ₜ[R] a)
    simp
  haveI t3 : IsScalarTower R A (k ⊗[R] B) := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B (k ⊗[R] B) r, IsScalarTower.algebraMap_apply R A B r]
    rfl
  haveI t4 : IsScalarTower k (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change a ⊗ₜ[R] (1 : B) = fibreMap R k A B (a ⊗ₜ[R] (1 : A))
    simp
  have h := isPushout_cancel R k A B (k ⊗[R] A) (k ⊗[R] B)
    TensorProduct.isPushout' TensorProduct.isPushout'
  exact (Algebra.isLocalization_iff_isPushout M B).mpr h.symm

end GlobalTheory.CompanionTheory.FinAlgFlat

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem fibreMap_flat_localize (R k P Q Bp An : Type*) [CommRing R] [CommRing k] [CommRing P]
    [CommRing Q] [CommRing Bp] [CommRing An] [Algebra R k] [Algebra R P] [Algebra R Q]
    [Algebra R Bp] [Algebra R An] [Algebra P Q] [Algebra P Bp] [Algebra P An] [Algebra Q An]
    [Algebra Bp An] [IsScalarTower R P Q] [IsScalarTower R P Bp] [IsScalarTower R Q An]
    [IsScalarTower R Bp An] [IsScalarTower P Q An] [IsScalarTower P Bp An]
    (M : Submonoid P) [IsLocalization M Bp] (N : Submonoid Q) [IsLocalization N An]
    (h : (fibreMap R k P Q).Flat) : (fibreMap R k Bp An).Flat := by
  have hQA : (fibreMap R k Q An).Flat := by
    have hl := fibreMap_isLocalization R k Q An N
    letI := (fibreMap R k Q An).toAlgebra
    exact IsLocalization.flat (k ⊗[R] An)
      (N.map (Algebra.TensorProduct.includeRight : Q →ₐ[R] k ⊗[R] Q))
  have e : (fibreMap R k Bp An).comp (fibreMap R k P Bp) =
      (fibreMap R k Q An).comp (fibreMap R k P Q) := by
    refine RingHom.ext fun x => ?_
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      simp [← IsScalarTower.algebraMap_apply]
  have hPA : ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).Flat := by
    rw [e]; exact h.comp hQA
  have hl := fibreMap_isLocalization R k P Bp M
  letI i1 := (fibreMap R k P Bp).toAlgebra
  letI i2 := (fibreMap R k Bp An).toAlgebra
  letI i3 := ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).toAlgebra
  haveI : IsScalarTower (k ⊗[R] P) (k ⊗[R] Bp) (k ⊗[R] An) := .of_algebraMap_eq' rfl
  exact (Module.flat_iff_of_isLocalization (k ⊗[R] Bp)
    (M.map (Algebra.TensorProduct.includeRight : P →ₐ[R] k ⊗[R] P)) (k ⊗[R] An)).mpr hPA

theorem flat_localization_of_fibre (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) (n : Ideal Q) [n.IsMaximal] :
    Module.Flat P (Localization.AtPrime n) := by
  haveI : Module.Finite P Q := .of_restrictScalars_finite R P Q
  haveI : Algebra.IsIntegral P Q := inferInstance
  haveI : Algebra.IsIntegral R P := inferInstance
  haveI : IsNoetherianRing P := IsNoetherianRing.of_finite R P
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite R Q
  let p : Ideal P := n.comap (algebraMap P Q)
  haveI hp : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := P) n
  have hmR : p.comap (algebraMap R P) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) p)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime n) :=
    (Localization.localRingHom p n (algebraMap P Q) rfl).toAlgebra
  haveI tP : IsScalarTower P (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n) x]
      exact (Localization.localRingHom_to_map p n (algebraMap P Q) rfl x).symm
  haveI tR : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R P (Localization.AtPrime p) x,
        ← IsScalarTower.algebraMap_apply P (Localization.AtPrime p) (Localization.AtPrime n),
        IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n),
        ← IsScalarTower.algebraMap_apply R P Q,
        ← IsScalarTower.algebraMap_apply R Q (Localization.AtPrime n)]
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n) :=
    IsLocalization.isNoetherianRing n.primeCompl _ inferInstance
  haveI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hnu
    have ham : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [← hmR, Ideal.mem_comap] at ham
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p
      (algebraMap R P a)).mpr ham
    rw [← IsScalarTower.algebraMap_apply R P (Localization.AtPrime p)] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime n)) :=
    Localization.isLocalHom_localRingHom p n (algebraMap P Q) rfl
  have hfl : Module.Flat R (Localization.AtPrime n) := inferInstance
  have hfib := fibreMap_flat_localize R (IsLocalRing.ResidueField R) P Q (Localization.AtPrime p)
    (Localization.AtPrime n) p.primeCompl n.primeCompl h
  have hBA : Module.Flat (Localization.AtPrime p) (Localization.AtPrime n) :=
    GlobalTheory.T.module_flat_of_flat_and_fibre_flat R (Localization.AtPrime p) (Localization.AtPrime n) hfl hfib
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime n)).mp hBA

theorem flat_of_fibreMap_flat (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) : Module.Flat P Q :=
  Module.flat_of_isLocalized_maximal Q Q (fun n _ => Localization.AtPrime n)
    (fun n _ => Algebra.linearMap Q _) (fun n _ => flat_localization_of_fibre R P Q h n)

theorem ringHom_flat_of_fibre_flat : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q),
    (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat →
      φ.toRingHom.Flat := by
  intro R P Q _ _ _ _ _ _ _ _ _ _ φ h
  letI : Algebra P Q := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R P Q := .of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : IsScalarTower.toAlgHom R P Q = φ := by ext; rfl
  have h' : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat := by
    rw [fibreMap, e]; exact h
  exact flat_of_fibreMap_flat R P Q h'

end GlobalTheory.CompanionTheory.FinAlgFlat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibreStatement

section

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.flat_of_flat_special_fibre : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q), (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat → φ.toRingHom.Flat := by
  first | exact @GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | exact GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat <;> assumption)
end
end
