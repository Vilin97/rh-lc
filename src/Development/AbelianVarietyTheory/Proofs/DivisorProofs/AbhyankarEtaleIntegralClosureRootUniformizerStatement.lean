module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarDvrOfIsSeparable
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
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarDvrOfIsSeparableStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.abhyankar_dvr_of_isSeparable_alt : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale D (integralClosure D (TensorProduct S D L)) := by
  first | (exact @GlobalTheory.abhyankar_dvr_of_isSeparable) | (exact GlobalTheory.abhyankar_dvr_of_isSeparable) | (intros; apply GlobalTheory.abhyankar_dvr_of_isSeparable  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTensorOfEtaleOfIsIntegral

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem exists_one_tmul_eq_of_isIntegral_smooth_fractionField
    (R K B : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (x : K ⊗[R] B) (hx : IsIntegral R x) : ∃ b : B, x = (1 : K) ⊗ₜ[R] b := by
  let e := Algebra.TensorProduct.comm R K B
  have h1 : IsIntegral R (e x) := hx.map e.toAlgHom
  have h2 : IsIntegral B (e x) := h1.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := B) (B := K)).2 ⟨e x, h2⟩
  have hy' : (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = e x := congrArg Subtype.val hy
  have key : ∀ y : B ⊗[R] integralClosure R K, ∃ b : B,
      (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = b ⊗ₜ[R] (1 : K) := by
    intro y
    induction y with
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, e.injective ?_⟩
  rw [← hy', hb]
  simp [e]

theorem etale_integralClosure_tensor_of_etale_of_isIntegral :
    ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  intro S₁ K₁ T _ _ _ _ _ _ _ _ hE hI
  let i : T →ₐ[S₁] K₁ ⊗[S₁] T := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S₁ K₁)
  have hint : ∀ t : T, i t ∈ integralClosure S₁ (K₁ ⊗[S₁] T) := fun t =>
    (Algebra.IsIntegral.isIntegral (R := S₁) t).map i
  let φ : T →ₐ[S₁] integralClosure S₁ (K₁ ⊗[S₁] T) := i.codRestrict _ hint
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := exists_one_tmul_eq_of_isIntegral_smooth_fractionField S₁ K₁ T x hx
      exact ⟨b, Subtype.ext hb.symm⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTensorOfEtaleOfIsIntegralStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_integralClosure_tensor : ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  first | (exact @GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (exact GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (intros; apply GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarEtaleIntegralClosureRootUniformizer

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing : ∀ (S K L F : Type) [CommRing S] [Field K] [Algebra S K] [IsFractionRing S K] [CommRing L]
    [Algebra K L] [Algebra S L] [IsScalarTower S K L] [CommRing F] [Algebra K F] [Algebra S F]
    [IsScalarTower S K F], Nonempty (F ⊗[S] L ≃ₐ[F] F ⊗[K] L) := by
  intro S K L F _ _ _ _ _ _ _ _ _ _ _ _
  have hb : IsBaseChange K (LinearMap.id : L →ₗ[S] L) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mp
      (isLocalizedModule_id (nonZeroDivisors S) L K)
  let g : K ⊗[S] L →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) (AlgHom.id S L) (fun _ _ => Commute.all _ _)
  have hg : (g : K ⊗[S] L → L) = hb.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp [g, IsBaseChange.equiv_tmul, Algebra.smul_def]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  let e0 : K ⊗[S] L ≃ₐ[K] L := AlgEquiv.ofBijective g (by rw [hg]; exact hb.equiv.bijective)
  exact ⟨(Algebra.TensorProduct.cancelBaseChange S K F F L).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl e0)⟩

theorem GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem : ∀ (D B F : Type) [CommRing D] [CommRing B] [Algebra D B] [CommRing F] [Algebra D F]
    (N : Subalgebra D B) (M : Submonoid D), (∀ m ∈ M, IsUnit (algebraMap D F m)) →
    (∀ b : B, ∃ m ∈ M, m • b ∈ N) →
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) := by
  intro D B F _ _ _ _ _ N M hM hN
  let Dm := Localization M
  have hM' : ∀ y : M, IsUnit (algebraMap D F y) := fun y => hM y y.2
  letI : Algebra Dm F := (IsLocalization.lift (M := M) (S := Dm) (g := algebraMap D F) hM').toAlgebra
  haveI : IsScalarTower D Dm F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq (M := M) (S := Dm) hM' x).symm)
  let ι : Dm ⊗[D] N →ₐ[Dm] Dm ⊗[D] B := Algebra.TensorProduct.map (AlgHom.id Dm Dm) N.val
  have hι : Function.Bijective ι := by
    constructor
    · have := Module.Flat.lTensor_preserves_injective_linearMap (M := Dm) N.val.toLinearMap
        Subtype.val_injective
      exact this
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul a b =>
        obtain ⟨m, hm, hmb⟩ := hN b
        let u := (IsLocalization.map_units Dm (⟨m, hm⟩ : M)).unit
        refine ⟨(a * ↑u⁻¹) ⊗ₜ[D] (⟨m • b, hmb⟩ : N), ?_⟩
        simp only [ι, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
        rw [← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        have hu : (u : Dm) = algebraMap D Dm m := rfl
        rw [← hu, mul_left_comm, Units.mul_inv, mul_one]
      | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
  let eι : Dm ⊗[D] N ≃ₐ[Dm] Dm ⊗[D] B := AlgEquiv.ofBijective ι hι
  let E : F ⊗[D] N ≃ₐ[F] F ⊗[D] B :=
    (Algebra.TensorProduct.cancelBaseChange D Dm F F N).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl eι).trans
        (Algebra.TensorProduct.cancelBaseChange D Dm F F B))
  have hE : ⇑(Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) = ⇑E := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f n =>
      simp [E, eι, ι, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [hE]
  exact E.bijective

theorem GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L] [Algebra.IsAlgebraic K L]
    [CommRing D] [Algebra S D], ∀ b : D ⊗[S] L,
    ∃ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), m • b ∈ integralClosure D (D ⊗[S] L) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ b
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | tmul d l =>
    obtain ⟨s, hs0, hint⟩ := IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff S K L).mpr (Algebra.IsAlgebraic.isAlgebraic l))
    refine ⟨algebraMap S D s, ⟨s, mem_nonZeroDivisors_of_ne_zero hs0, rfl⟩, ?_⟩
    have h1 : algebraMap S D s • (d ⊗ₜ[S] l) = algebraMap D (D ⊗[S] L) d * ((1 : D) ⊗ₜ[S] (s • l)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        algebraMap_smul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.tmul_smul]
    rw [h1]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ d) ?_
    exact (hint.map (Algebra.TensorProduct.includeRight : L →ₐ[S] D ⊗[S] L)).tower_top
  | add x y hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 * m2, mul_mem hm1 hm2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Subalgebra.smul_mem _ h1 _
    · rw [mul_smul]; exact Subalgebra.smul_mem _ h2 _

theorem GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  intro S S₁ K K₁ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy hram hsep
  let f : S[X] := X ^ q - C π
  let D := AdjoinRoot f
  have hD : Algebra.Etale D (integralClosure D (D ⊗[S] L)) :=
    GlobalTheory.T.abhyankar_dvr_of_isSeparable_alt S K L π q D ⟨AlgEquiv.refl⟩ hπ hqu hram hsep
  let φ : D →ₐ[S] S₁ := AdjoinRoot.liftAlgHom f (Algebra.ofId S S₁) y (by simp [f, hy])
  letI : Algebra D S₁ := φ.toRingHom.toAlgebra
  letI : Algebra D K₁ := ((algebraMap S₁ K₁).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower D S₁ K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower S D S₁ := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  haveI : IsScalarTower S D K₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply S S₁ K₁, IsScalarTower.algebraMap_apply S D S₁]; rfl)
  let N := integralClosure D (D ⊗[S] L)
  let T := S₁ ⊗[D] N
  haveI : Algebra.Etale S₁ T := Algebra.Etale.baseChange D N S₁
  haveI : Algebra.IsIntegral S₁ T := Algebra.IsIntegral.tensorProduct D S₁ N
  haveI hT := GlobalTheory.T.etale_integralClosure_tensor S₁ K₁ T inferInstance inferInstance
  have hunit : ∀ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), IsUnit (algebraMap D K₁ m) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S S₁ K₁]
    refine IsUnit.mk0 _ ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective S₁ K₁), map_eq_zero_iff _ hinj]
    exact nonZeroDivisors.ne_zero hs
  let e1 : K₁ ⊗[S₁] T ≃ₐ[K₁] K₁ ⊗[D] N := Algebra.TensorProduct.cancelBaseChange D S₁ K₁ K₁ N
  let e2 : K₁ ⊗[D] N ≃ₐ[K₁] K₁ ⊗[D] (D ⊗[S] L) :=
    AlgEquiv.ofBijective _ (GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem D (D ⊗[S] L) K₁ N _ hunit (GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor S K L D))
  let e3 : K₁ ⊗[D] (D ⊗[S] L) ≃ₐ[K₁] K₁ ⊗[S] L := Algebra.TensorProduct.cancelBaseChange S D K₁ K₁ L
  obtain ⟨e4⟩ := GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing S K L K₁
  let e : K₁ ⊗[S₁] T ≃ₐ[S₁] K₁ ⊗[K] L := (((e1.trans e2).trans e3).trans e4).restrictScalars S₁
  exact Algebra.Etale.of_equiv e.mapIntegralClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarEtaleIntegralClosureRootUniformizerStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  first | (exact @GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (exact GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (intros; apply GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer  <;> assumption)
end
end
