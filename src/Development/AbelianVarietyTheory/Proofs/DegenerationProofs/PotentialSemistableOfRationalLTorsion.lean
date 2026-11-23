module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTame
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusCountsIntegralTorsionSpecialFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisActionTorsionPairingTameFixedPointsStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightLeAddOfTorsionPairingStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTameStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) := by
  first | exact @GlobalTheory.SS.exists_maxUnramified_frobenius_tame | exact GlobalTheory.SS.exists_maxUnramified_frobenius_tame | (intros; apply GlobalTheory.SS.exists_maxUnramified_frobenius_tame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevelStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_neronNeutralComponent_finite_level : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  first | exact @GlobalTheory.NeutralLevel.exists_level_model | exact GlobalTheory.NeutralLevel.exists_level_model | (intros; apply GlobalTheory.NeutralLevel.exists_level_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpSchemePointsModelOverField

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.ModelPoints

theorem exists_push_equiv {S S' : Scheme.{0}} (f : S' ⟶ S) (H : Over S) [GrpObj H] (T : Over S')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H),
      ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_comp_equiv {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (e : G ≅ H) [IsMonHom e.hom]
    (T : Over S) : ∃ π : (T ⟶ G) ≃* (T ⟶ H), ∀ y, π.symm y = y ≫ e.inv :=
  ⟨{ toFun := fun x => x ≫ e.hom
     invFun := fun y => y ≫ e.inv
     left_inv := fun x => by simp
     right_inv := fun x => by simp
     map_mul' := fun x y => MonObj.mul_comp x y e.hom }, fun _ => rfl⟩

theorem exists_equiv {S₁ S₂ S : Scheme.{0}} (f : S ⟶ S₁) (g : S ⟶ S₂) (A : Over S₁) [GrpObj A]
    (G : Over S₂) [GrpObj G] (e : (Over.pullback g).obj G ≅ (Over.pullback f).obj A) [IsMonHom e.hom]
    {T : Scheme.{0}} (t : T ⟶ S) (s₁ : T ⟶ S₁) (s₂ : T ⟶ S₂) (h₁ : s₁ = t ≫ f) (h₂ : s₂ = t ≫ g) :
    ∃ θ : (Over.mk s₁ ⟶ A) ≃* (Over.mk s₂ ⟶ G), ∀ (x : Over.mk s₁ ⟶ A) (z : T ⟶ pullback A.hom f),
      z ≫ pullback.fst A.hom f = x.left → z ≫ pullback.snd A.hom f = t →
      (θ x).left = z ≫ e.inv.left ≫ pullback.fst G.hom g := by
  obtain ⟨π₁, p₁⟩ := exists_push_equiv f A (Over.mk t) s₁ h₁
  obtain ⟨π₂, p₂⟩ := exists_push_equiv g G (Over.mk t) s₂ h₂
  obtain ⟨π, p⟩ := exists_comp_equiv e (Over.mk t)
  refine ⟨π₁.symm.trans (π.symm.trans π₂), fun x z hz hz' => ?_⟩
  have hx : π₁.symm x = Over.homMk z hz' := by
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hz.symm.trans (p₁ (Over.homMk z hz')).symm)
  show (π₂ (π.symm (π₁.symm x))).left = _
  rw [p₂, p, hx, Over.comp_left, Category.assoc]
  rfl

theorem spMap_comp_of_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap h = spMap g ≫ spMap f := by
  subst e
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem spMap_cancel {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {g : B →+* C}
    (hg : Function.Injective g) {a b : Sp B ⟶ Sp A} (e : spMap g ≫ a = spMap g ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e
  congr 1
  ext x
  exact hg (congrArg (fun q => q.hom x) e)

theorem points_model : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  intro K W L _ _ _ _ _ A _ G _ ⟨e, he⟩ Ω _ _ _ j hK hW
  obtain ⟨θ, hθ⟩ := exists_equiv (spMap (algebraMap K L)) (spMap (algebraMap W L)) A G e (spMap j)
    _ _ (spMap_comp_of_eq hK) (spMap_comp_of_eq hW)
  refine ⟨θ, fun τ hτ x x' hx => ?_, fun K' _ i j' hj x y hy ρ hρ => ?_⟩
  · have w : x.left ≫ A.hom = spMap j ≫ spMap (algebraMap K L) :=
      (Over.w x).trans (spMap_comp_of_eq hK)
    rw [hθ x (pullback.lift x.left (spMap j) w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
      hθ x' (spMap τ ≫ pullback.lift x.left (spMap j) w)
        (by rw [Category.assoc, pullback.lift_fst, hx])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hτ]), Category.assoc]
  · have w : y ≫ A.hom = spMap i ≫ spMap (algebraMap K L) := by
      apply spMap_cancel j'.injective
      rw [← Category.assoc, hy, ← Category.assoc, ← spMap_comp_of_eq hj]
      exact (Over.w x).trans (spMap_comp_of_eq hK)
    have w' : (pullback.lift y (spMap i) w ≫ e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap W L))) ≫ G.hom
        = spMap ρ := by
      have h₁ : e.inv.left ≫ pullback.snd G.hom (spMap (algebraMap W L))
          = pullback.snd A.hom (spMap (algebraMap K L)) := Over.w e.inv
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% h₁, pullback.lift_snd_assoc]
      exact (spMap_comp_of_eq hρ.symm).symm
    have hU : spMap j' ≫ spMap ρ = spMap (algebraMap W Ω) :=
      (spMap_comp_of_eq (by rw [hρ, ← RingHom.comp_assoc, hj, hW])).symm
    let U : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap ρ) := Over.homMk (spMap j') hU
    let y' : Over.mk (spMap ρ) ⟶ G := Over.homMk _ w'
    have hxy : θ x = U ≫ y' := by
      apply Over.OverMorphism.ext
      rw [hθ x (spMap j' ≫ pullback.lift y (spMap i) w)
        (by rw [Category.assoc, pullback.lift_fst, hy])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hj]), Category.assoc]
      rfl
    refine ⟨y', fun c => ?_⟩
    rw [map_pow, hxy, ← MonObj.comp_pow]
    rfl

end GlobalTheory.SS.ModelPoints
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpSchemePointsModelOverFieldStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.grpScheme_points_model_over_field : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  first | exact @GlobalTheory.SS.ModelPoints.points_model | exact GlobalTheory.SS.ModelPoints.points_model | (intros; apply GlobalTheory.SS.ModelPoints.points_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpeciaStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.isSemiAbelian_of_proper_generic_torusExtension_special : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by
  first | exact @GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension | exact GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension | (intros; apply GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsion

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem iter_lift {R K Ω : Type} [CommRing R] [Field K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
    (I : Ideal R) (φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ q ∈ I) (n : ℕ) (x : R) :
    ∃ y : R, algebraMap R Ω y = (φ ^ n) (algebraMap R Ω x) ∧ y - x ^ (q ^ n) ∈ I := by
  induction n with
  | zero => exact ⟨x, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hI⟩ := ih
    obtain ⟨z, hz, hJ⟩ := h y
    refine ⟨z, by rw [hz, hy, pow_succ', AlgEquiv.mul_apply], ?_⟩
    rw [← Ideal.Quotient.eq] at hI hJ ⊢
    rw [hJ, map_pow, hI, ← map_pow, ← pow_mul, pow_succ]

theorem pow_pow_fixed {k : Type} [Monoid k] (c : k) (a : ℕ) (h : c ^ a = c) (n : ℕ) : c ^ (a ^ n) = c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_lift_frac {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (g : A →+* L) (hg : Function.Injective g) : ∃ j : K →+* L, j.comp (algebraMap A K) = g :=
  ⟨IsFractionRing.lift hg, RingHom.ext fun a => IsFractionRing.lift_algebraMap hg a⟩

theorem isSemiAbelian_of_rational_torsion (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l)
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left)
    (W L R K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V W] [Algebra K L] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K'] [Algebra R K'] [IsFractionRing R K']
    [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω] [IsLocalHom (algebraMap W R)]
    (hWR : Function.Injective (algebraMap W R)) (hRΩ : Function.Injective (algebraMap R Ω))
    (hcW : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hVΩ : (algebraMap W Ω).comp (algebraMap V W) = (algebraMap K Ω).comp (algebraMap V K))
    (hk : IsAlgClosed (IsLocalRing.ResidueField R)) (hlR : IsUnit (l : R))
    (p r₀ f : ℕ) (hp : p.Prime) (hpR : CharP (IsLocalRing.ResidueField R) p) (hr₀ : 1 ≤ r₀) (hf : 1 ≤ f)
    (hres : ∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r₀) ^ m) = c)
    (σ φ : Ω ≃ₐ[K] Ω) (hfix : ∀ w : W, (φ ^ f) (algebraMap W Ω w) = algebraMap W Ω w)
    (hφ : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ (p ^ r₀) ∈ IsLocalRing.maximalIdeal R)
    (hζ : ∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ (p ^ r₀))
    (hL : ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L,
      φ (σ x) = (σ ^ (p ^ r₀)) (φ x) ∧ (σ x = x → ∃ a b : R, algebraMap R Ω b ≠ 0 ∧ x * algebraMap R Ω b = algebraMap R Ω a))
    (G : Over (Sp W)) [GrpObj G] (hG : SmConn G) (hmod : IsModel (L := L) P.A G)
    (hdim : SmoothOfRelativeDimension P.g G.hom)
    (N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left)
    (hN : AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N)
    (c : ℕ) (hc : 1 ≤ c)
    (hext : ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left,
      s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left) :
    IsSemiAbelian G := by
  classical
  obtain ⟨j', hj0⟩ := exists_lift_frac (K := K') (algebraMap R Ω) hRΩ
  have hj' : ∀ x : R, j' (algebraMap R K' x) = algebraMap R Ω x := fun x => RingHom.congr_fun hj0 x
  obtain ⟨i, hi⟩ := exists_lift_frac (K := L) ((algebraMap R K').comp (algebraMap W R))
    ((IsFractionRing.injective R K').comp hWR)
  replace hi := hi.symm
  have hjW : (j'.comp i).comp (algebraMap W L) = algebraMap W Ω := by
    rw [RingHom.comp_assoc, ← hi]
    exact RingHom.ext fun w => (hj' _).trans (IsScalarTower.algebraMap_apply W R Ω w).symm
  have hjK : (j'.comp i).comp (algebraMap K L) = algebraMap K Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) ?_
    rw [RingHom.comp_assoc, ← hcW, ← RingHom.comp_assoc, hjW, hVΩ]
  obtain ⟨θ, hθ, hθK⟩ := GlobalTheory.T.grpScheme_points_model_over_field K W L P.A G hmod Ω (j'.comp i) hjK hjW
  obtain ⟨e, act, hact, he, hpair, hrel, hdef⟩ := GlobalTheory.T.galois_action_torsion_pairing_tame_fixedPoints K P Ω l (p ^ r₀) hl htors σ φ K' j' hζ
    (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
      obtain ⟨a, b, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
      refine ⟨algebraMap R _ a / algebraMap R _ b, ?_⟩
      rw [map_div₀, hj', hj', div_eq_iff hb0]
      exact hab.symm⟩)
  have hcard := (GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl).1
  haveI := P.isAb.comm
  have hψ : (φ ^ f).toRingEquiv.toRingHom.comp (j'.comp i) = j'.comp i := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors W) ?_
    rw [RingHom.comp_assoc, hjW]
    exact RingHom.ext fun w => hfix w
  obtain ⟨t, a, m, C, Q, H, U, hm, hH, hcnt, hQ, hU, hHU, hT⟩ :=
    GlobalTheory.T.frobenius_counts_integral_torsion_specialFibre W R Ω hRΩ hk p (r₀ * f) l hp hpR (Nat.mul_pos hr₀ hf) hl hlR
      (fun c => by
        obtain ⟨m, hm, h⟩ := hres c
        refine ⟨m, hm, ?_⟩
        rw [pow_mul, ← pow_mul _ f m, mul_comm f m, pow_mul _ m f]
        exact pow_pow_fixed c _ h f)
      (φ ^ f).toRingEquiv.toRingHom (fun w => hfix w)
      (fun x => by rw [pow_mul]; exact iter_lift _ φ _ hφ f x)
      G hG P.g hdim N hN (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) θ (act (φ ^ f))
      (fun x => hθ _ hψ _ _ (hact _ x))
  rw [← map_pow, ← pow_mul] at hU hHU
  have hqq : (p ^ (r₀ * f)) ^ m = (p ^ r₀) ^ (f * m) := by rw [pow_mul, ← pow_mul _ f m]
  rw [hqq] at hU hQ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hg : P.g ≤ t + a := by
    refine GlobalTheory.T.weight_le_add_of_torsion_pairing (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) Ω l ((p ^ r₀) ^ (f * m)) P.g t a c C hl h3
      (Nat.cast_ne_zero.2 hl.ne_zero) ?_ hc hcard e he (act σ) (act (φ ^ (f * m))) (hpair _) (hrel _)
      (fun x hx => Over.OverMorphism.ext ((hact σ x).trans (htors σ x hx))) H U Q ?_ hcnt hQ hU hHU
    · rw [← pow_mul]
      exact Nat.one_lt_pow (Nat.mul_pos hr₀ (Nat.mul_pos hf hm)).ne' hp.one_lt
    · intro n x hx hS
      obtain ⟨y, hy⟩ := hdef n x hx hS
      obtain ⟨y', hy'⟩ := hθK K' i j' rfl x y hy _ hi
      obtain ⟨s, hs₁, hs₂⟩ := hext y'
      refine (hH _).2 ⟨s, hs₁, ?_⟩
      rw [← hy', ← hs₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj0]
  have hproper : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    obtain ⟨ε, -⟩ := hmod
    haveI := P.isAb.proper
    rw [← Over.w ε.hom]
    have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj P.A).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    have : IsIso ε.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ε.hom))
    infer_instance
  · clear hcard
    refine GlobalTheory.T.isSemiAbelian_of_proper_generic_torusExtension_special W L G hG hproper _ _ ?_ ?_ (hT hg)
    · ext w
      rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
    · intro z
      obtain ⟨m, hm, h⟩ := hres z
      have h1 : 1 < (p ^ r₀) ^ m := by
        rw [← pow_mul]
        exact Nat.one_lt_pow (Nat.mul_pos hr₀ hm).ne' hp.one_lt
      refine ⟨Polynomial.X ^ ((p ^ r₀) ^ m) - Polynomial.X, ?_, by simp [h]⟩
      refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) ?_
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast h1

theorem potentialSemistable_rational_lTorsion_any_closure (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (IsLocalRing.ResidueField V)) (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l) (hlu : IsUnit (l : V))
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) :
    PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  classical
  obtain ⟨R, _, σ, φ, hSH, hloc, hres, hW, hσ, hφ, hζ, hL⟩ := GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt V K hfin l hl hlu Ω _ rfl
  letI := Fintype.ofFinite (IsLocalRing.ResidueField V)
  obtain ⟨p, hpV⟩ := CharP.exists (IsLocalRing.ResidueField V)
  obtain ⟨r₀, hp, hq⟩ := FiniteField.card (IsLocalRing.ResidueField V) p
  rw [← Nat.card_eq_fintype_card] at hq
  rw [hq] at hres hφ hζ hL
  have hpR : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_ringHom (IsLocalRing.ResidueField.map (algebraMap V R)).injective p
  have hVΩ : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hRΩ : Function.Injective (algebraMap R Ω) := Subtype.val_injective
  have hVR : Function.Injective (algebraMap V R) := fun a b h => hVΩ (congrArg Subtype.val h)
  obtain ⟨K', _, _, hSH⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra R K'), SH R K' := ⟨_, _, _, hSH⟩
  haveI : IsFractionRing R K' := hSH.2.2.2
  obtain ⟨jK, hjK'⟩ := exists_lift_frac (K := K) ((algebraMap R K').comp (algebraMap V R))
    ((IsFractionRing.injective R K').comp hVR)
  letI : Algebra K K' := jK.toAlgebra
  have hcomp : (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) := hjK'.symm
  obtain ⟨s, c, hc, hgeo⟩ := GlobalTheory.T.exists_neronNeutralComponent_finite_level V K R K' hSH hcomp P
  obtain ⟨W, hWd, hs, hWc, hWf, hWl, f, hf, hfix⟩ := hW s
  obtain ⟨G, _, L, _, _, _, _, hG, hcW, hmod, hdim, ⟨N, hN⟩, hext⟩ := hgeo W hWd hs hWl
  have hlR : IsUnit (l : R) := by simpa using hlu.map (algebraMap V R)
  haveI : IsLocalHom (algebraMap W R) := hWl
  have hsemi : IsSemiAbelian G :=
    isSemiAbelian_of_rational_torsion V K l hl h3 P Ω htors W L R K' Subtype.val_injective hRΩ hcW
      (IsScalarTower.algebraMap_eq V K Ω) hSH.2.2.1 hlR p r₀ f hp hpR r₀.2 hf hres σ φ (fun w => hfix w.1 w.2) hφ hζ
      (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
        obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hab⟩⟩)
      G hG hmod hdim N hN c hc hext
  have hVW : IsLocalHom (algebraMap V W) := ⟨fun v hv => by
    have : IsUnit (algebraMap V R v) := hv.map W.val
    exact (isUnit_map_iff (algebraMap V R) v).1 this⟩
  exact ⟨W, L, inferInstance, inferInstance, hWd, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcW, hWf, hVW, hWc, G, inferInstance, hmod, hsemi⟩

theorem potModel_of_rational_torsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hfin l hl h3 hlu P htors
  exact potentialSemistable_rational_lTorsion_any_closure V K hfin l hl h3 hlu P (AlgebraicClosure K) htors

end GlobalTheory.SS
end
end
