module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriesTransportUniformisingIsoStatement
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTraitScalarGenericFibreNonfield

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unit_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  intro R _ _ _ D C W _ _ _ T Z p p' hpp hR b hb z

  have hw : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ jK R := by
    rw [← T.ξ_π, ← C.gp_π, ← Category.assoc T.G.hom, ← T.cart.1.w, ← Category.assoc C.A.A.hom, ← C.α_cart.1.w]
    simp only [← Category.assoc]; rw [hpp]
  have hpt := congrArg (fun g => (g z).asIdeal) hw
  simp only [Scheme.Hom.comp_apply] at hpt
  set P := ((p ≫ T.G.hom) z) with hP
  have hc : P.asIdeal.comap T.φ = ⊥ := by
    have e1 : (spMap T.φ ((T.G.hom) (p z))).asIdeal = P.asIdeal.comap T.φ := by
      rw [hP, Scheme.Hom.comp_apply]; rfl
    rw [← e1, hpt]
    have e2 : ((jK R) ((C.A.A.hom) (p' z))).asIdeal = ((C.A.A.hom) (p' z)).asIdeal.comap (algebraMap R (FractionRing R)) := rfl
    rw [e2]
    have hbot : ((C.A.A.hom) (p' z)).asIdeal = ⊥ := by
      have := ((C.A.A.hom) (p' z)).isPrime
      exact Ideal.eq_bot_of_prime _
    rw [hbot]
    exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
  have hdvr : IsDiscreteValuationRing W := T.cdvr.1
  have hPbot : P.asIdeal = ⊥ := by
    by_contra hne
    have hmax : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime hne
    have hm : P.asIdeal = maximalIdeal W := IsLocalRing.eq_maximalIdeal hmax
    have hRm : maximalIdeal R ≠ ⊥ := fun h => hR ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRm
    have hl := T.loc
    have hφr : T.φ r ∈ P.asIdeal := by
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hr (isUnit_of_map_unit T.φ r hu)
    have : r ∈ P.asIdeal.comap T.φ := hφr
    rw [hc] at this
    exact hr0 ((Submodule.mem_bot R).1 this)
  have hmem : (p ≫ T.G.hom) z ∈ (Sp W).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) := by
    rw [basicOpen_eq_of_affine]
    show b ∉ ((p ≫ T.G.hom) z).asIdeal
    rw [← hP, hPbot]; exact fun h => hb ((Submodule.mem_bot W).1 h)
  have hpull : gs p z ⊤ (scal T.G.hom b) = gs (p ≫ T.G.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) :=
    gs_pull p T.G.hom z ⊤ trivial _
  rw [hpull, gs_eq _ z ⊤ trivial]
  have hz : z ∈ Z.basicOpen (((p ≫ T.G.hom).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hmem
  exact (Scheme.mem_basicOpen Z _ z (by trivial)).1 hz

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTraitScalarGenericFibreNonfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isUnit_trait_scalar_genericFibre_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  first | exact @GlobalTheory.Mum.unit_nonfield | exact GlobalTheory.Mum.unit_nonfield | (intros; apply GlobalTheory.Mum.unit_nonfield <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitScalarCancelOfIsField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CancelField

theorem isIso_jK {R : Type} [CommRing R] [IsDomain R] (hR : IsField R) : IsIso (jK R) := by
  have hb : Function.Bijective (algebraMap R (FractionRing R)) :=
    ⟨IsFractionRing.injective R (FractionRing R), IsFractionRing.surjective_iff_isField.2 hR⟩
  have : IsIso (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem isIso_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (hR : IsField R) : IsIso M.gp := by
  haveI := isIso_jK hR
  haveI := M.integral
  haveI := M.proper
  haveI := M.dominant
  haveI : IsClosedImmersion M.gp :=
    isClosedImmersion_of_comp_eq_id (M.π ≫ inv (jK R)) M.gp (by rw [← Category.assoc, M.gp_π, IsIso.hom_inv_id])
  haveI : Surjective M.gp := ⟨by
    have h1 := M.gp.isClosedEmbedding.isClosed_range
    have h2 := M.gp.denseRange
    exact Set.range_eq_univ.1 (h1.closure_eq ▸ h2.closure_range)⟩
  exact isIso_of_isClosedImmersion_of_surjective M.gp

theorem sval_comp {X Y₀ Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (p : Z ⟶ Y) (r : Y ⟶ Y₀) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s (p ≫ r) z J = (p.stalkMap z).hom (sval s r (p z) (fun ψ => J (p ≫ ψ))) := by
  have hJ' : Good L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  rw [sval_of s (p ≫ r) z J (fun k => J (p ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp p r z _ (hJ'.mem φ r) _

theorem scal_cancel {W : Type} [CommRing W] [IsDomain W] {Y : Scheme.{0}} (f : Y ⟶ Sp W) [Flat f] (y : Y) {b : W}
    (hb : b ≠ 0) {u v : Y.presheaf.stalk y}
    (h : gs (𝟙 Y) y ⊤ (scal f b) * u = gs (𝟙 Y) y ⊤ (scal f b) * v) : u = v := by
  set c : Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b with hc
  have e1 : gs (𝟙 Y) y ⊤ (scal f b) = (f.stalkMap y).hom (gs (𝟙 (Sp W)) (f y) ⊤ c) := by
    have := gs_pull (𝟙 Y) f y ⊤ trivial c
    rw [Category.id_comp] at this
    refine this.trans ?_
    have := gs_comp f (𝟙 (Sp W)) y ⊤ trivial c
    rwa [Category.comp_id] at this
  have hc0 : c ≠ 0 := by
    intro h0
    apply hb
    have hi : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1
    exact hi (h0.trans (map_zero _).symm)
  have he0 : gs (𝟙 (Sp W)) (f y) ⊤ c ≠ 0 := by
    rw [gs_eq (𝟙 (Sp W)) (f y) ⊤ trivial]
    intro h0
    apply hc0
    have hi := germ_injective_of_isIntegral (Sp W) (U := (𝟙 (Sp W)) ⁻¹ᵁ ⊤) (f y) trivial
    have := hi (h0.trans (map_zero _).symm)
    exact this
  letI := (f.stalkMap y).hom.toAlgebra
  haveI : Module.Flat _ (Y.presheaf.stalk y) := Flat.stalkMap f y
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y) (mem_nonZeroDivisors_of_ne_zero he0)
  apply hreg
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [← e1]
  exact h

end GlobalTheory.Mum.CancelField

namespace GlobalTheory.Mum


open GlobalTheory.Mum.CancelField in
theorem cancel_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k σ s b c hR hb H Z p p' hp z J hJ
  haveI : IsIso C.α := C.α_cart.1.isIso_fst_of_isIso (isIso_gp C.toModif hR)
  haveI : Smooth C.G.hom := C.semi.smooth
  haveI : Flat C.G.hom := inferInstance
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  obtain ⟨q, hq⟩ : ∃ q : T.G.left ⟶ C.A.A.left, q ≫ C.α = T.β := ⟨T.β ≫ inv C.α, by simp⟩
  have key : ∀ y J', Good C.P.L.L y J' → sval σ (𝟙 _) y J' = gs q y ⊤ (scal C.A.A.hom c) * sval s q y J' := by
    intro y J' hJ'
    exact scal_cancel T.G.hom y hb (H _ (𝟙 _) q (by rw [hq, Category.id_comp]) y J' hJ')
  obtain rfl : p' = p ≫ q := (cancel_mono C.α).1 (by rw [Category.assoc, hq]; exact hp.symm)
  have hJ' : Good C.P.L.L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  have e1 := sval_comp σ p (𝟙 _) z J hJ
  rw [Category.comp_id] at e1
  rw [e1, sval_comp s p q z J hJ, gs_comp p q z ⊤ trivial, ← map_mul, key (p z) _ hJ']

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitScalarCancelOfIsFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.trait_scalar_cancel_of_isField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  first | exact @GlobalTheory.Mum.cancel_field | exact GlobalTheory.Mum.cancel_field | (intros; apply GlobalTheory.Mum.cancel_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarsRescale

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitRescale

variable {X Z : Scheme.{0}}

noncomputable def gsTop (f : Z ⟶ X) (z : Z) : Γ(X, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (f ⁻¹ᵁ ⊤) z trivial).hom.comp (f.app ⊤).hom

theorem gs_top (f : Z ⟶ X) (z : Z) (a : Γ(X, ⊤)) : gs f z ⊤ a = gsTop f z a := gs_eq f z ⊤ trivial a

theorem scal_comp {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ spMap φ) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem scal_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) (x y : A) :
    scal q (x * y) = scal q x * scal q y := by simp only [scal, map_mul]

theorem scal_one {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) : scal q 1 = 1 := by
  simp only [scal, map_one]

theorem gs_top_mul (f : Z ⟶ X) (z : Z) (a b : Γ(X, ⊤)) : gs f z ⊤ (a * b) = gs f z ⊤ a * gs f z ⊤ b :=
  gs_mul f z ⊤ trivial a b

theorem gs_top_one (f : Z ⟶ X) (z : Z) : gs f z ⊤ 1 = 1 := by rw [gs_top, map_one]

theorem gs_scal {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem gs_scal_compat {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  rw [scal_comp, scal_comp, gs_scal, gs_scal]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem sval_smul {Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (a • s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  unfold sval
  rw [show (a • s).f (fun k => J (r ≫ φ k)) = resG Y le_top a * s.f (fun k => J (r ≫ φ k)) from
    GlobalTheory.LB.smul_f a s _]
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

end GlobalTheory.Mum.TraitRescale


open GlobalTheory.Mum.TraitRescale in
theorem GlobalTheory.Mum.Trait.exp_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b : W) (u : Wˣ) (c₁ c₂ : R), a ≠ 0 → c₂ ≠ 0 → T.φ c₂ * (u : W) * a = T.φ c₁ * b → T.Exp a b s F → T.Exp 1 u (scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • s) F := by
  intro R _ _ _ hB D C W _ _ _ T k s F a b u c₁ c₂ ha hc₂ hrel hExp
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hagree⟩ := hExp
  obtain ⟨σ'', hcar''⟩ := GlobalTheory.T.exists_carries_transport_uniformising_iso R D C W T k (u : W) σ'
  refine ⟨σ'', ⟨σ', f', hcar'', hpull, hexp⟩, ?_⟩
  have hφ2 : T.φ c₂ ≠ 0 := fun h0 => hc₂ (T.inj (h0.trans (map_zero T.φ).symm))
  have hb : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hrel
    exact (mul_ne_zero (mul_ne_zero hφ2 u.ne_zero) ha) hrel
  set c : FractionRing R := algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂ with hc
  have hc₂K : algebraMap R (FractionRing R) c₂ ≠ 0 :=
    fun h0 => hc₂ (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  have hcc : c * algebraMap R (FractionRing R) c₂ = algebraMap R (FractionRing R) c₁ := div_mul_cancel₀ _ hc₂K
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ'' p z J =
        gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J) := by
    intro Z p p' h z J hJ
    choose J' hJ' using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
    have e1 := hcar Z p z J J' hJ hJ'
    have e2 := hcar'' Z p z J J' hJ hJ'
    have e3 := hagree Z p p' h z J hJ

    have m : gs p z ⊤ (scal T.G.hom (T.φ c₂)) * gs p z ⊤ (scal T.G.hom (u : W)) * gs p z ⊤ (scal T.G.hom a) =
        gs p z ⊤ (scal T.G.hom (T.φ c₁)) * gs p z ⊤ (scal T.G.hom b) := by
      have := congrArg (fun w => gs p z ⊤ (scal T.G.hom w)) hrel
      simpa only [scal_mul, gs_top_mul] using this
    rw [gs_scal_compat T p p' h z c₁, gs_scal_compat T p p' h z c₂] at m
    have hC : gs p' z ⊤ (scal C.A.A.hom c) * gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) =
        gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₁)) := by
      rw [← hcc, scal_mul, gs_top_mul]
    have hU : IsUnit (gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) := by
      obtain ⟨v, hv⟩ := Ne.isUnit hc₂K
      have : IsUnit (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) :=
        IsUnit.of_mul_eq_one (scal C.A.A.hom ((v⁻¹ : (FractionRing R)ˣ) : FractionRing R))
          (by rw [← scal_mul, ← hv, Units.mul_inv, scal_one])
      rw [gs_top]
      exact this.map _
    have e13 := e1.symm.trans e3
    rw [e2]
    apply hU.mul_right_cancel
    linear_combination (gs p z ⊤ (scal T.G.hom (u : W)) *
      gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) * e13 + sval s p' z J * m -
      (gs p z ⊤ (scal T.G.hom b) * sval s p' z J) * hC
  intro Z p p' h z J hJ
  rw [scal_one, gs_top_one, _root_.one_mul, sval_smul C.P.L.L _ s p' z hJ]
  by_cases hF : IsField R
  · exact GlobalTheory.T.trait_scalar_cancel_of_isField R hB D C W T k σ'' s b c hF hb key Z p p' h z J hJ
  · exact (GlobalTheory.T.isUnit_trait_scalar_genericFibre_nonfield R D C W T Z p p' h hF b hb z).mul_left_cancel (key Z p p' h z J hJ)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarsRescaleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.trait_expansionScalars_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b : W) (u : Wˣ) (c₁ c₂ : R), a ≠ 0 → c₂ ≠ 0 → T.φ c₂ * (u : W) * a = T.φ c₁ * b → T.Exp a b s F → T.Exp 1 u (scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • s) F := by
  first | exact @GlobalTheory.Mum.Trait.exp_rescale | exact GlobalTheory.Mum.Trait.exp_rescale | (intros; apply GlobalTheory.Mum.Trait.exp_rescale <;> assumption)
end
end
