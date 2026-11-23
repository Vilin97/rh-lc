module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZeroStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClass

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isOb2 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w
  have hθ : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ θ : Ω[F.obj T⁄R₀] →+ L.B T'',
      IsTheta I (L.p T) ((L.ρ b).comp (L.ρ a)) (L.ρ (a ≫ b)) θ := by
    intro T T' T'' a b
    obtain ⟨θ, hθ, -⟩ := (theta_classify R R₀ (L.B T) (F.obj T) (L.B T'') I hI π hπ (L.p T) (L.semi T)
      (L.surj T) (L.ker T) ((L.ρ b).comp (L.ρ a))).1 (L.ρ (a ≫ b)) (fun x ↦ by
        rw [← L.ker T'', map_sub, AlgHom.comp_apply, L.nat, L.nat, L.nat, mp_comp, sub_self])
    exact ⟨θ, hθ⟩
  choose θ hθ using hθ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = θ T T' T'' a b (w.1 T) := fun T T' T'' a b ↦
    (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
      (L.ker T'') (σ T'') (hσ T'')).2.2.2 _ ((hθ T T' T'' a b).mem _)
  choose z hzK hzσ using hz
  have key : ∀ (T T' T'' T''' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T''') (x : Ω[F.obj T⁄R₀]),
      L.ρ c (θ T T' T'' a b x) + θ T T'' T''' (a ≫ b) c x =
        θ T T' T''' a (b ≫ c) x + θ T' T'' T''' b c (p1 F a x) := by
    intro T T' T'' T''' a b c x
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T'') (L.B T''') _ _ _
      (hθ T T' T'' a b)).1 (L.ρ c)
    have s1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h1).2.1 (hθ T T'' T''' (a ≫ b) c)
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T''') (L.B T''') _ _ _
      (hθ T' T'' T''' b c)).2 (L.ρ a) (mp F a) (L.nat a)
    have s2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h2).2.1 (hθ T T' T''' a (b ≫ c))
    rw [Category.assoc] at s1
    rw [AlgHom.comp_assoc] at s2
    have e := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ (L.ρ (a ≫ b ≫ c)) _ _ s1).2.2.1 s2
    have ex := DFunLike.congr_fun e x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply] at ex
    exact ex.trans (add_comm _ _)
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add (f := _), k1, k2, k3, k4, sub_self, add_zero]
    · rw [em, map_sub, map_add (f := _), map_add (f := _), ← (nat.1 _), hzσ, hzσ, hzσ, hzσ, w.2 a, key, sub_self]
  exact ⟨H2.mk _ ⟨_, hZ⟩, θ, σ, ⟨_, hZ⟩, hθ, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, hzσ T T' T'' a b⟩⟩

end GlobalTheory.Obs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClassStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_degreeTwoObstructionClass : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  first | exact @GlobalTheory.Obs.exists_isOb2 | exact GlobalTheory.Obs.exists_isOb2 | (intros; apply GlobalTheory.Obs.exists_isOb2 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaEq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem isTheta_eq {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {I : Ideal R} {p : B →+* B₀} (hp : Function.Surjective p)
    {α β : B →ₐ[R] B'} {θ₁ θ₂ : Ω[B₀⁄R₀] →+ B'} (h₁ : IsTheta I p α β θ₁) (h₂ : IsTheta I p α β θ₂) :
    θ₁ = θ₂ := by
  ext w
  have hw : w ∈ Submodule.span B₀ (Set.range (D R₀ B₀)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun z _ ↦ θ₁ z = θ₂ z) ?_ ?_ ?_ ?_ hw
  · rintro z ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := hp y
    rw [h₁.der, h₂.der]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add (f := _), map_add (f := _), hy, hz]
  · intro c z _ hz
    obtain ⟨b, rfl⟩ := hp c
    rw [h₁.smul, h₂.smul, hz]

theorem isSig_eq {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {I : Ideal R}
    {π : R →+* R₀} (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    {p : B →+* B₀} (hp : Function.Surjective p) {σ σ' : R₁ ⊗[R₀] B₀ →+ B} (h : α.IsSig p σ) (h' : α.IsSig p σ') :
    σ = σ' := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y x =>
    obtain ⟨b, rfl⟩ := hp x
    rw [h, h']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isOb2_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w w' : Glob1 F) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsOb2 α w c → L.IsOb2 α w' c' → L.IsOb2 α (w + w') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w w' c c' h h'
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h
  obtain ⟨θ', σ', z', hθ', hσ', rfl, hz'⟩ := h'
  refine ⟨θ, σ, z + z', hθ, hσ, (map_add _ _ _).symm, fun T T' T'' a b ↦ ?_⟩
  have eθ : θ T T' T'' a b = θ' T T' T'' a b := isTheta_eq (L.surj T) (hθ T T' T'' a b) (hθ' T T' T'' a b)
  have eσ : σ T'' = σ' T'' := isSig_eq α (L.surj T'') (hσ T'') (hσ' T'')
  obtain ⟨k₁, s₁⟩ := hz T T' T'' a b
  obtain ⟨k₂, s₂⟩ := hz' T T' T'' a b
  have ez : (z + z').1 T T' T'' a b = z.1 T T' T'' a b + z'.1 T T' T'' a b := rfl
  refine ⟨?_, ?_⟩
  · unfold Aug.KerQ at k₁ k₂ ⊢
    rw [ez, map_add (f := _), k₁, k₂, add_zero]
  · rw [ez, map_add (f := _), s₁, eσ, s₂, ← eθ]
    exact (map_add (θ T T' T'' a b) (w.1 T) (w'.1 T)).symm

end GlobalTheory.Obs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFun

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem rho_id_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀}
    {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀} (L : Pre I π F) (hL : L.IsFun) (T : C) (y : L.B T) :
    L.ρ (𝟙 T) y = y := by
  set e := L.ρ (𝟙 T) with he
  have idem : ∀ x, e (e x) = e x := fun x ↦ by
    have := hL (𝟙 T) (𝟙 T) x
    rw [Category.comp_id] at this
    exact this.symm
  have hJ := LiftSys.map_sq hI (L.B T)
  have memJ : ∀ x, x - e x ∈ I.map (algebraMap R (L.B T)) := fun x ↦ by
    rw [← L.ker]
    rw [map_sub, L.nat, mp_id, sub_self]
  have sq0 : ∀ u v, u ∈ I.map (algebraMap R (L.B T)) → v ∈ I.map (algebraMap R (L.B T)) → u * v = 0 := by
    intro u v hu hv
    have : u * v ∈ I.map (algebraMap R (L.B T)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hu hv
    rw [hJ] at this
    simpa using this
  have fix : ∀ z ∈ I.map (algebraMap R (L.B T)), e z = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, -, rfl⟩ := hx
      exact e.commutes i
    | zero => exact map_zero e
    | add x w _ _ hx hw => rw [map_add (f := _), hx, hw]
    | smul b x hxm hx =>
      rw [smul_eq_mul, map_mul, hx]
      have := sq0 _ _ (memJ b) hxm
      rw [sub_mul] at this
      exact (sub_eq_zero.1 this).symm
  have h1 := fix _ (memJ y)
  rw [map_sub, idem, sub_self] at h1
  exact (sub_eq_zero.1 h1.symm).symm

theorem nonempty_sys_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ L hL
  exact ⟨{
    F := {
      obj := L.B
      map := fun a ↦ CommAlgCat.ofHom (L.ρ a)
      map_id := fun T ↦ CommAlgCat.hom_ext (AlgHom.ext fun y ↦ rho_id_eq hI L hL T y)
      map_comp := fun a b ↦ CommAlgCat.hom_ext (AlgHom.ext fun x ↦ hL a b x) }
    p := L.p
    semi := L.semi
    nat := fun a b ↦ L.nat a b
    surj := L.surj
    ker := L.ker
    smooth := L.smooth }⟩

end GlobalTheory.Obs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFunStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_squareZeroSmoothLiftSystem_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  first | exact @GlobalTheory.Obs.nonempty_sys_of_isFun | exact GlobalTheory.Obs.nonempty_sys_of_isFun | (intros; apply GlobalTheory.Obs.nonempty_sys_of_isFun <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftAbelianSchemeSquareZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.exists_smooth_lift_of_abelian : FormSt → PrimitiveExtendedDegTwoVanish → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) ∧ Smooth X.hom := by
  intro hF hP R R₀ _ _ I hI π hπ hk A₀ _ g hab hsm
  haveI := hsm
  haveI : Smooth A₀.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A₀ ⊗ A₀).hom := inferInstanceAs (Smooth (Limits.pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ I hI π hπ hk
  obtain ⟨hPar, hProj, hadd⟩ := hF R₀ A₀ g hab hsm
  obtain ⟨L⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff A₀.hom) (fun T ↦ smooth_sec_affine A₀.hom T.unop)
  obtain ⟨L₂⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff (A₀ ⊗ A₀).hom)
    (fun T ↦ smooth_sec_affine (A₀ ⊗ A₀).hom T.unop)
  have key : ∀ w, L.IsOb2 α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L w
    have nat : ∀ (f : A₀ ⊗ A₀ ⟶ A₀) (w' : GlobForm (A₀ ⊗ A₀).hom) (c' : CatCoh.H2 (ext R₁ (OAff (A₀ ⊗ A₀).hom))),
        IsPullForm (overW f) w w' → L₂.IsOb2 α w' c' → IsExtendedPullbackDegTwo R₁ (overW f) c c' := by
      intro f w' c' hw hc'
      refine GlobalTheory.T.degreeTwoObstructionClass_natural R R₀ I hI π hπ hk R₁ α _ (OAff A₀.hom) _ (OAff (A₀ ⊗ A₀).hom) _ (pairFst f.left)
        (pairPull (overW f)) L L₂ w w' c c' (fun T ↦ ?_) hc hc'
      exact (congrArg (fun z : Glob1 (OPair f.left (A₀ ⊗ A₀).hom) ↦ z.1 T) hw).trans
        (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff (A₀ ⊗ A₀).hom) (pairFst f.left) T _)
    obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (fst A₀ A₀)) w)
    obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (snd A₀ A₀)) w)
    have hm : pullForm (overW μ[A₀]) w = pullForm (overW (fst A₀ A₀)) w + pullForm (overW (snd A₀ A₀)) w :=
      hadd w _ _ _ (isPullForm_pullForm _ w) (isPullForm_pullForm _ w) (isPullForm_pullForm _ w)
    have hcm : L₂.IsOb2 α (pullForm (overW μ[A₀]) w) (c₁ + c₂) := by
      rw [hm]; exact isOb2_add R R₀ I hI π hπ hk R₁ α _ _ L₂ _ _ c₁ c₂ hc₁ hc₂
    have h0 : c = 0 := hP R₀ R₁ α.q α.sq A₀ g hab hsm c c₁ c₂
      (nat _ _ _ (isPullForm_pullForm _ w) hcm) (nat _ _ _ (isPullForm_pullForm _ w) hc₁)
      (nat _ _ _ (isPullForm_pullForm _ w) hc₂)
    rw [← h0]; exact hc
  obtain ⟨L', hL'⟩ := GlobalTheory.T.exists_functorial_lifts_of_obstructionTwo_zero R R₀ I hI π hπ hk R₁ α _ A₀.hom hPar hProj L key
  obtain ⟨S⟩ := GlobalTheory.T.nonempty_squareZeroSmoothLiftSystem_of_isFun R R₀ I hI π hπ hk _ A₀.hom L' hL'
  obtain ⟨X, s, i, hci, hsi, ⟨hpres⟩⟩ := GlobalTheory.LiftGlue.exists_presents R R₀ I hI π hπ hk _ A₀.hom S
  obtain ⟨hpb, hsmooth⟩ := GlobalTheory.LiftSys.presents_isLift R R₀ I hI π hπ hk _ A₀.hom S X s i hci hsi hpres
  exact ⟨Over.mk s, i, hpb, hsmooth⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftAbelianSchemeSquareZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_smooth_lift_abelian_scheme_square_zero : FormSt → PrimitiveExtendedDegTwoVanish → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) ∧ Smooth X.hom := by
  first | exact @GlobalTheory.Obs.exists_smooth_lift_of_abelian | exact GlobalTheory.Obs.exists_smooth_lift_of_abelian | (intros; apply GlobalTheory.Obs.exists_smooth_lift_of_abelian <;> assumption)
end
end
