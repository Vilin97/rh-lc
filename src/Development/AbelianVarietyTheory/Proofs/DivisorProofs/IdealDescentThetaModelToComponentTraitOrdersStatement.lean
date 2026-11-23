module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamificationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelSmoothOfRelativeDimensionCharZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImageStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZEqMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitRam

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem dim_eq (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : T.A.g = g := by
  let K := AlgebraicClosure (FractionRing T.V)
  let k : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap (FractionRing T.V) K)
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp := (IsPullback.of_hasPullback T.A.A.hom k).paste_horiz T.cart.1
  have h1 : SmoothOfRelativeDimension T.A.g (pullback.snd T.A.A.hom k) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback T.A.A.hom k) T.A.smoothDim
  refine GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (k ≫ T.y) ?_
  change SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (k ≫ T.y))
  rw [← hp.isoPullback_inv_snd]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (fst := hp.isoPullback.inv) (g := 𝟙 _) ⟨by simp⟩) h1

theorem finrank_le (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := by
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  have e := dim_eq hn hζ T
  omega

theorem evalZ_eq_mul : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o), 2 ≤ n → IsUnit ζ → ∀ (F : SFam g n ζ) (T T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun ℤ, IsPolFan id g φ → φ.evalZ T'.β = m * φ.evalZ T.β := by
  intro g n o _ ζ hn hζ F T T' f fK hf hl hK hy m hm φ hφ
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n o ζ F T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB inferInstance hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    (by rw [pow_one]; rfl)
  have hon := hφ T.D.toPre.X (finrank_le hn hζ T)
  have hc : toReal T.β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := T.D.toPre.X) :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.Poinc.TraitRam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i := by
  first | exact @GlobalTheory.Poinc.traitLift_setup | exact GlobalTheory.Poinc.traitLift_setup | (intros; apply GlobalTheory.Poinc.traitLift_setup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealThetaModelToClopenComponent

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.NormDown

theorem dvd_of_map_dvd {V V' : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {x y : V} (hxy : h x ∣ h y) : x ∣ y := by
  rcases ValuationRing.dvd_total x y with hd | ⟨c, rfl⟩
  · exact hd
  · by_cases hy : y = 0
    · simp [hy]
    obtain ⟨e, he⟩ := hxy
    have hy' : h y ≠ 0 := fun h0 => hy (hi (by rw [h0, map_zero]))
    have h1 : h y * 1 = h y * (h c * e) := by rw [mul_one, ← mul_assoc, ← map_mul, ← he]
    have hu : IsUnit (h c) := isUnit_iff_exists_inv.2 ⟨e, (mul_left_cancel₀ hy' h1).symm⟩
    have hc : IsUnit c := (isUnit_map_iff h c).1 hu
    exact ⟨↑hc.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem map_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {I I' : Ideal V} (e : I.map h = I'.map h) : I = I' := by
  obtain ⟨x, rfl⟩ : ∃ x, I = Ideal.span {x} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, I' = Ideal.span {y} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I').symm⟩
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd (dvd_of_map_dvd h hi e.dvd) (dvd_of_map_dvd h hi e.symm.dvd)

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  have idlAlong_eq_map_local {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
      (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    have hx : χ (closedPoint R) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [idlAlong_eq_map_local J χ ⟨U, hU⟩ hle, idlAlong_eq_map_local J _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z Z X₁.π X₁.fin inferInstance hLN X₁.normal hZ.2.1
    (by rw [hπ]; exact hWc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V T.complete (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = T₂.y ≫ i := by
    intro χ hχ
    rw [Category.assoc, hχ, ← Category.assoc, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'),
      jK_spMap f fK hfK, Category.assoc, hgen, hy₂]
    simp only [Category.assoc]
  obtain ⟨a₀, ha₀, h₀⟩ := hord T₂ _ (hover (spMap f ≫ ξ₁) (Category.assoc _ _ _))
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord T₂ _ (hover (ψ j) (hψ j))
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← idlAlong_comp_local, hcomp, Category.assoc, h₀, hmp]
  simp only [← idlAlong_comp_local, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.NormDown
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealThetaModelToClopenComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  first | exact @GlobalTheory.NormDown.normDescent | exact GlobalTheory.NormDown.normDescent | (intros; apply GlobalTheory.NormDown.normDescent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentThetaModelToComponentTraitOrders

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.PoincDown

theorem exists_assoc_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {ϖ : V} (hϖ : Irreducible ϖ)
    {ϖ' : V'} (hϖ' : Irreducible ϖ') : ∃ m : ℕ, 1 ≤ m ∧ Associated (f ϖ) (ϖ' ^ m) := by
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ'
  refine ⟨m, Nat.one_le_iff_ne_zero.2 fun e => ?_, hm⟩
  subst e
  rw [pow_zero] at hm
  exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hm))

theorem map_eq_span_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) {ϖ' : V'} (hϖ' : Irreducible ϖ') {m : ℕ}
    (hm : Associated (f ϖ) (ϖ' ^ m)) {I : Ideal V} {b : ℕ} (h : I.map f = Ideal.span {ϖ' ^ b}) :
    ∃ a : ℕ, b = m * a ∧ I = Ideal.span {ϖ ^ a} := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact pow_ne_zero _ hϖ'.ne_zero h
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨a, ?_, rfl⟩
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton] at h
  have h2 : Associated (ϖ' ^ (m * a)) (ϖ' ^ b) := by
    rw [pow_mul]; exact (hm.pow_pow (n := a)).symm.trans h
  have e1 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.dvd
  have e2 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.symm.dvd
  omega

theorem idealDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  obtain ⟨k, J, hk, hJs, hJo⟩ := GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  refine ⟨k * ι, J, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hJs, ?_⟩
  intro T ξ hξ hW
  have hc : IsClopen (Set.range X₁.π) := by rw [hπ]; exact hWc
  obtain ⟨T', f, fK, ξ₁, hf, hfl, hfK, hy, hsq, hgen⟩ := GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension g n F Z i W8 X₁ hc T ξ hξ (by rw [hπ]; exact hW)
  obtain ⟨a₁, ha₁, hJ₁⟩ := hord T' ξ₁ hgen
  have hJ := hJo T' ξ₁ hgen
  obtain ⟨m, hm1, hm⟩ := exists_assoc_pow f hf T.irr T'.irr
  have hφ' := GlobalTheory.Poinc.TraitRam.evalZ_eq_mul g n _ _ (by omega) (cycBase (show n ≠ 0 by omega)).ζ.isUnit F T T' f fK hf hfl hfK hy m hm φ hφ
  have e1 : (idlAlong J ξ).map f = Ideal.span {T'.ϖ ^ (a₁ * k)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hsq, hJ, hJ₁, Ideal.span_singleton_pow, ← pow_mul]
  obtain ⟨a, hb, ha⟩ := map_eq_span_pow f T.irr T'.irr hm e1
  refine ⟨a, ?_, ha⟩
  have hb' : ((a₁ : ℝ) * k) = m * a := by exact_mod_cast hb
  rw [ha₁, hφ'] at hb'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  apply mul_left_cancel₀ hm0.ne'
  linarith [hb']

end GlobalTheory.PoincDown
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentThetaModelToComponentTraitOrdersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.PoincDown.idealDescent | exact GlobalTheory.PoincDown.idealDescent | (intros; apply GlobalTheory.PoincDown.idealDescent <;> assumption)
end
end
