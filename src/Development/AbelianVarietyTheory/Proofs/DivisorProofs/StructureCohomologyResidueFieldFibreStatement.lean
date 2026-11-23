module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimLEIsLocalRingQuotPow
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomSplitBaseChange

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SplitCx

variable {R : Type} [CommRing R]

theorem exists_quasiInv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (d : M →ₗ[R] N) (hQ : Module.Projective R (N ⧸ LinearMap.range d)) :
    ∃ b : N →ₗ[R] M, ∀ x, d (b (d x)) = d x := by
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y : N, y - t ((LinearMap.range d).mkQ y) ∈ LinearMap.range d := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun ht ((LinearMap.range d).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let r : N →ₗ[R] LinearMap.range d :=
    LinearMap.codRestrict _ (LinearMap.id - t ∘ₗ (LinearMap.range d).mkQ) hmem
  have hr : ∀ y : LinearMap.range d, r y = y := by
    intro y
    apply Subtype.ext
    simp only [r, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 y.2, map_zero, sub_zero]
  haveI : Module.Projective R (LinearMap.range d) :=
    Module.Projective.of_split (LinearMap.range d).subtype r (LinearMap.ext hr)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict d)
  refine ⟨s ∘ₗ r, fun x => ?_⟩
  have h1 := LinearMap.congr_fun hs (r (d x))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
  have h2 := congrArg Subtype.val h1
  have h3 : (r (d x) : N) = d x := congrArg Subtype.val (hr ⟨d x, LinearMap.mem_range_self d x⟩)
  exact h2.trans h3

theorem exists_decomp {M0 M1 M2 : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [Module.Projective R M1] [Module.Projective R M2]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (h : ∀ x, d1 (d0 x) = 0)
    (hQ1 : Module.Projective R (M1 ⧸ LinearMap.range d0))
    (hQ2 : Module.Projective R (M2 ⧸ LinearMap.range d1)) :
    ∃ (e : M1 →ₗ[R] M1) (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1),
      e ∘ₗ e = e ∧ e ∘ₗ d0 = 0 ∧ d1 ∘ₗ e = 0 ∧ LinearMap.id = e + d0 ∘ₗ a + b ∘ₗ d1 := by
  obtain ⟨b, hb⟩ := exists_quasiInv d1 hQ2
  obtain ⟨b', hb'⟩ := exists_quasiInv d0 hQ1
  set a : M1 →ₗ[R] M0 := b' ∘ₗ (LinearMap.id - b ∘ₗ d1) with ha
  set e : M1 →ₗ[R] M1 := LinearMap.id - d0 ∘ₗ a - b ∘ₗ d1 with he0
  have he : ∀ y, e y = y - d0 (b' (y - b (d1 y))) - b (d1 y) := fun y => by
    simp [e, a]
  have k1 : ∀ x, d1 (e x) = 0 := fun x => by
    rw [he]; simp only [map_sub, h, hb]; abel
  have k2 : ∀ x, d0 (b' (e x)) = 0 := fun x => by
    rw [he]; simp only [map_sub, hb']; abel
  refine ⟨e, a, b, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply]
    simp only [he (e x), k1, map_zero, sub_zero, k2]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    simp only [he, h, map_zero, sub_zero, hb', sub_self]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, k1]
  · ext x
    simp only [e, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

theorem bc {M0 M1 M2 P : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [AddCommGroup P] [Module R P]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (π : M1 →ₗ[R] P) (σ : P →ₗ[R] M1)
    (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1)
    (hπσ : π ∘ₗ σ = LinearMap.id) (hπd : π ∘ₗ d0 = 0) (hdσ : d1 ∘ₗ σ = 0)
    (hid : LinearMap.id = σ ∘ₗ π + d0 ∘ₗ a + b ∘ₗ d1) (S : Type) [CommRing S] [Algebra R S] :
    Function.Surjective (fun z : LinearMap.ker (d1.baseChange S) => π.baseChange S z.1) ∧
      ∀ z : LinearMap.ker (d1.baseChange S),
        π.baseChange S z.1 = 0 ↔ z.1 ∈ LinearMap.range (d0.baseChange S) := by
  have e1 : ∀ y, π.baseChange S (σ.baseChange S y) = y := fun y => by
    have := congrArg (LinearMap.baseChange S) hπσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at this
    exact LinearMap.congr_fun this y
  have e2 : ∀ y, π.baseChange S (d0.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hπd
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e3 : ∀ y, d1.baseChange S (σ.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hdσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e4 : ∀ y, y = σ.baseChange S (π.baseChange S y) + d0.baseChange S (a.baseChange S y)
      + b.baseChange S (d1.baseChange S y) := fun y => by
    have := congrArg (LinearMap.baseChange S) hid
    rw [LinearMap.baseChange_id, LinearMap.baseChange_add, LinearMap.baseChange_add,
      LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.baseChange_comp] at this
    exact LinearMap.congr_fun this y
  refine ⟨fun y => ⟨⟨σ.baseChange S y, e3 y⟩, e1 y⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · refine ⟨a.baseChange S z.1, ?_⟩
    have h0 : d1.baseChange S z.1 = 0 := z.2
    have := e4 z.1
    rw [hz, h0, map_zero, map_zero, zero_add, add_zero] at this
    exact this.symm
  · rintro ⟨w, hw⟩
    rw [← hw]; exact e2 w

end GlobalTheory.AbCoh.SplitCx

namespace GlobalTheory.AbCoh

theorem cohom_split_baseChange : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z := by
  intro R _ K hK hQ i h1 h2 R' _ _
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  try simp only [Nat.add_sub_cancel, Nat.add_one_sub_one]
  haveI : Module.Projective R (K.X (j + 1)) := (hK _).2
  haveI : Module.Projective R (K.X (j + 1 + 1)) := (hK _).2
  haveI : Module.Finite R (K.X (j + 1)) := (hK _).1
  have hdd : ∀ x, (K.d (j + 1) (j + 1 + 1)).hom ((K.d j (j + 1)).hom x) = 0 := fun x => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]; rfl
  obtain ⟨e, a, b, hee, hed, hde, hid⟩ := SplitCx.exists_decomp (K.d j (j + 1)).hom
    (K.d (j + 1) (j + 1 + 1)).hom hdd (hQ j (by omega)) (hQ (j + 1) (by omega))
  let π : K.X (j + 1) →ₗ[R] LinearMap.range e := e.rangeRestrict
  let σ : LinearMap.range e →ₗ[R] K.X (j + 1) := (LinearMap.range e).subtype
  have hπσ : π ∘ₗ σ = LinearMap.id := by
    ext ⟨y, w, rfl⟩
    change e (e w) = e w
    rw [← LinearMap.comp_apply, hee]
  have hπd : π ∘ₗ (K.d j (j + 1)).hom = 0 := by
    ext x
    change e ((K.d j (j + 1)).hom x) = 0
    rw [← LinearMap.comp_apply, hed]; rfl
  have hdσ : (K.d (j + 1) (j + 1 + 1)).hom ∘ₗ σ = 0 := by
    ext ⟨y, w, rfl⟩
    change (K.d (j + 1) (j + 1 + 1)).hom (e w) = 0
    rw [← LinearMap.comp_apply, hde]; rfl
  have hid' : LinearMap.id = σ ∘ₗ π + (K.d j (j + 1)).hom ∘ₗ a + b ∘ₗ (K.d (j + 1) (j + 1 + 1)).hom := by
    rw [hid]; rfl
  haveI : Module.Projective R (LinearMap.range e) := Module.Projective.of_split σ π hπσ
  obtain ⟨sR, kR⟩ := SplitCx.bc _ _ π σ a b hπσ hπd hdσ hid' R
  obtain ⟨sR', kR'⟩ := SplitCx.bc _ _ π σ a b hπσ hπd hdσ hid' R'
  refine ⟨LinearMap.range e, inferInstance, inferInstance, inferInstance, inferInstance,
    (TensorProduct.lid R _).toLinearMap ∘ₗ (π.baseChange R ∘ₗ (LinearMap.ker _).subtype),
    π.baseChange R' ∘ₗ (LinearMap.ker _).subtype, ?_, sR', ?_, kR', ?_⟩
  · exact (TensorProduct.lid R _).surjective.comp sR
  · intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype,
      LinearEquiv.map_eq_zero_iff]
    exact kR z
  · intro z z' hz
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
    rw [hz]
    clear hz
    induction (z.1 : R ⊗[R] K.X (j + 1)) using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [ext, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, Algebra.ofId_apply,
        LinearMap.baseChange_tmul, TensorProduct.lid_tmul]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, _root_.mul_one]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]

end GlobalTheory.AbCoh
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapAlgHomAlgebraMap

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbCoh.CohBaseChange

theorem exists_equiv_of_ker {S M A B : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup A]
    [Module S A] [AddCommGroup B] [Module S B] (f : M →ₗ[S] A) (g : M →ₗ[S] B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ z, f z = 0 ↔ g z = 0) : ∃ e : A ≃ₗ[S] B, ∀ z, e (f z) = g z := by
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext z; exact h z
  refine ⟨(f.quotKerEquivOfSurjective hf).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    g.quotKerEquivOfSurjective hg, fun z ↦ ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f z) = Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, this]
  rfl

variable {R : Type} [CommRing R]

theorem dB_ext (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' R'' : Type} [CommRing R'] [Algebra R R']
    [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i j : ℕ) (y : R' ⊗[R] K.X i) :
    dB K R'' i j (ext α _ y) = ext α _ (dB K R' i j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem spMap_algHom_algebraMap {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R'']
    (α : R' →ₐ[R] R'') : spMap (α : R' →+* R'') ≫ spMap (algebraMap R R') = spMap (algebraMap R R'') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, α.comp_algebraMap]

theorem isPullback_self {X : Scheme.{0}} (s : X ⟶ Sp R) : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
  have : spMap (algebraMap R R) = 𝟙 (Sp R) := Spec.map_id _
  rw [this]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem liftsAt_of (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (i : ℕ) {H H₀ : Type} [AddCommGroup H] [Module R' H]
    [AddCommGroup H₀] [Module k H₀] (θ : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] H)
    (θ₀ : LinearMap.ker (dB K k i (i + 1)) →ₗ[k] H₀) (p : H → H₀) (hθ : Function.Surjective θ)
    (hθ₀ : ∀ z, θ₀ z = 0 ↔ z.1 ∈ LinearMap.range (dB K k (i - 1) i))
    (nat : ∀ z z', z'.1 = ext α _ z.1 → θ₀ z' = p (θ z)) (hp : Function.Surjective p) : LiftsAt K α i := by
  intro z hz
  obtain ⟨x, hx⟩ := hp (θ₀ ⟨z, hz⟩)
  obtain ⟨y, rfl⟩ := hθ x
  have hy' : ext α _ y.1 ∈ LinearMap.ker (dB K k i (i + 1)) := by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 y.2, map_zero]
  have h1 := nat y ⟨_, hy'⟩ rfl
  obtain ⟨b, hb⟩ := (hθ₀ (⟨z, hz⟩ - ⟨_, hy'⟩)).1 (by rw [map_sub, h1, hx, sub_self])
  refine ⟨y.1, b, y.2, ?_⟩
  rw [hb]
  simp

theorem bc_of {R' : Type} [CommRing R'] [Algebra R R'] {Z Z' P H H' : Type} [AddCommGroup Z] [Module R Z]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H]
    [AddCommGroup H'] [Module R' H'] (u : Z →ₗ[R] P) (v : Z' →ₗ[R'] R' ⊗[R] P) (θ : Z →ₗ[R] H)
    (θ' : Z' →ₗ[R'] H') (p : H → H') (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ') (h : ∀ z, θ z = 0 ↔ u z = 0)
    (h' : ∀ z, v z = 0 ↔ θ' z = 0) (nat : ∀ z, ∃ z', v z' = 1 ⊗ₜ u z ∧ θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e, he⟩ := exists_equiv_of_ker θ u hθ hu h
  obtain ⟨e', he'⟩ := exists_equiv_of_ker v θ' hv hθ' h'
  refine ⟨e.baseChange R R' _ _ ≪≫ₗ e', fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hθ c
  obtain ⟨z', h1, h2⟩ := nat z
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, he, ← h1, he', h2]

variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}

theorem liftsAt_zero (M : Model s K) (hU : UConst s) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (hα : Function.Surjective α) : LiftsAt K α 0 := by
  intro z hz
  have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
  have h₀ := IsPullback.of_hasPullback s (spMap (algebraMap R k))
  obtain ⟨e', -⟩ := M.θ0_one h'
  obtain ⟨e₀, he₀⟩ := M.θ0_one h₀
  obtain ⟨r, hr, -⟩ := hU k _ _ _ h₀ (M.θ0 h₀ ⟨z, hz⟩).1 (M.θ0 h₀ ⟨z, hz⟩).2
  have hz' : (⟨z, hz⟩ : LinearMap.ker (dB K k 0 1)) = r • ⟨_, e₀⟩ := by
    apply (M.θ0 h₀).injective
    rw [map_smul]
    refine Subtype.ext (funext fun T ↦ ?_)
    rw [hr T, Algebra.algebraMap_eq_smul_one, ← he₀ T]
    rfl
  obtain ⟨r', rfl⟩ := hα r
  refine ⟨r' • ((1 : R') ⊗ₜ[R] M.one), 0, ?_, ?_⟩
  · rw [map_smul]
    exact (congrArg (r' • ·) (LinearMap.mem_ker.1 e')).trans (smul_zero _)
  · have := congrArg Subtype.val hz'
    simp only [Submodule.coe_smul] at this
    rw [this, map_zero, add_zero, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp

theorem of_parts (hex : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧ Nonempty (Model s K))
    (halg : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) → (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) → ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom))
    (hsplit : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z) :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  intro R _ _ X s hp hf hU hl
  obtain ⟨K, hK, hb, ⟨M⟩⟩ := hex R X s hp hf
  have hproj := halg R K hK hb (by
    intro i hi R' _ _ _ _ k _ _ α hα
    have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
    have w := IsPullback.of_hasPullback (pullback.snd s (spMap (algebraMap R R'))) (spMap (α : R' →+* k))
    have h₀ := w.paste_horiz h'
    rw [spMap_algHom_algebraMap] at h₀
    obtain ⟨s1, s2⟩ := hl R' k α hα _ _ _ _ _ _ h' w
    obtain ⟨n1, n2⟩ := M.nat h' h₀ α _ w.w rfl
    obtain ⟨a1, -, a2, -⟩ := M.exact h'
    obtain ⟨-, b1, -, b2⟩ := M.exact h₀
    interval_cases i
    · exact liftsAt_zero M hU α hα
    · exact liftsAt_of K α 1 (M.θ1 h') (M.θ1 h₀) _ a1 b1 n1 s1
    · exact liftsAt_of K α 2 (M.θ2 h') (M.θ2 h₀) _ a2 b2 n2 s2)
  have hid := isPullback_self s
  obtain ⟨a1, b1, a2, b2⟩ := M.exact hid
  have hz : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (i : ℕ) (z : LinearMap.ker (dB K R i (i + 1))),
      ext (Algebra.ofId R R') _ z.1 ∈ LinearMap.ker (dB K R' i (i + 1)) := fun R' _ _ i z ↦ by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 z.2, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ1 hid) hu a1 fun z ↦ (ku z).trans (b1 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ2 hid) hu a2 fun z ↦ (ku z).trans (b2 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R'
    obtain ⟨c1, d1, -, -⟩ := M.exact h
    obtain ⟨n1, -⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ1 hid) (M.θ1 h) _ hu hv a1 c1 (fun z ↦ (b1 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d1 z).symm) fun z ↦ ⟨⟨_, hz R' 1 z⟩, hn _ _ rfl, n1 _ _ rfl⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R'
    obtain ⟨-, -, c2, d2⟩ := M.exact h
    obtain ⟨-, n2⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ2 hid) (M.θ2 h) _ hu hv a2 c2 (fun z ↦ (b2 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d2 z).symm) fun z ↦ ⟨⟨_, hz R' 2 z⟩, hn _ _ rfl, n2 _ _ rfl⟩

end GlobalTheory.AbCoh.CohBaseChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibre

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.CohBaseChange

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s :=
  of_parts (@GlobalTheory.AbCoh.exists_finite_projective_model) (@GlobalTheory.AbCoh.projective_coker_of_liftsAt) (@GlobalTheory.AbCoh.cohom_split_baseChange)

end GlobalTheory.AbCoh.CohBaseChange
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.structure_cohomology_residue_field_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  first | exact @GlobalTheory.AbCoh.CohBaseChange.main | exact GlobalTheory.AbCoh.CohBaseChange.main | (intros; apply GlobalTheory.AbCoh.CohBaseChange.main <;> assumption)
end
end
