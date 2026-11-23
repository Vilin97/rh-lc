module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalFirstNeighbourhoodRetractionForms
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH2BijectiveStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsAcyclicOfTwoSectionsRetraction

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory

theorem coef_acyclic_of_two_sections (C : Type 1) [Category.{0} C] (M : Coef C) (S : C ⥤ C) (u v : 𝟭 C ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (hr : ∀ (T T' : C) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x))
    (hu : ∀ T x, r T (M.map (u.app T) x) = 0) (hv : ∀ T x, r T (M.map (v.app T) x) = x) :
    M.Ac0 ∧ M.Ac1 ∧ M.Ac2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    funext T
    have h1 : g (S.obj T) = M.map (u.app T) (g T) := hg T (S.obj T) (u.app T)
    have h2 : g (S.obj T) = M.map (v.app T) (g T) := hg T (S.obj T) (v.app T)
    have e := hv T (g T)
    rw [← h2, h1, hu] at e
    exact e.symm
  · intro f hf
    refine ⟨fun T ↦ r T (f T (S.obj T) (u.app T) - f T (S.obj T) (v.app T)), ?_⟩
    intro T T' φ
    have key : ∀ θ : 𝟭 C ⟶ S, r T' (M.map (θ.app T') (f T T' φ)) + r T' (f T' (S.obj T') (θ.app T')) =
        M.map φ (r T (f T (S.obj T) (θ.app T))) + r T' (f (S.obj T) (S.obj T') (S.map φ)) := by
      intro θ
      have nat : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have e1 := hf T T' (S.obj T') φ (θ.app T')
      have e2 := hf T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
      rw [nat, e2] at e1
      have e3 := congrArg (r T') e1
      simp only [map_add (f := _), hr] at e3
      exact e3.symm
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) kv - ku
  · intro z hz
    let A : (𝟭 C ⟶ S) → ∀ (T T' : C) (_ : T ⟶ T'), M.obj (S.obj T') := fun θ T T' φ ↦
      z T T' (S.obj T') φ (θ.app T') - z T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
    refine ⟨fun T T' φ ↦ r T' (A v T T' φ - A u T T' φ), ?_⟩
    intro T T' T'' φ ψ
    have key : ∀ θ : 𝟭 C ⟶ S, M.map ψ (r T' (A θ T T' φ)) =
        r T'' (M.map (θ.app T'') (z T T' T'' φ ψ)) + r T'' (A θ T T'' (φ ≫ ψ)) - r T'' (A θ T' T'' ψ)
          - r T'' (z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ)) := by
      intro θ
      have nat1 : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have nat2 : ψ ≫ θ.app T'' = θ.app T' ≫ S.map ψ := θ.naturality ψ
      have h1 := hz T T' T'' (S.obj T'') φ ψ (θ.app T'')
      have h2 := hz T T' (S.obj T') (S.obj T'') φ (θ.app T') (S.map ψ)
      have h3 := hz T (S.obj T) (S.obj T') (S.obj T'') (θ.app T) (S.map φ) (S.map ψ)
      rw [nat1, ← nat2] at h2
      rw [← S.map_comp] at h3
      have inner : M.map (S.map ψ) (A θ T T' φ) =
          M.map (θ.app T'') (z T T' T'' φ ψ) + A θ T T'' (φ ≫ ψ) - A θ T' T'' ψ
            - z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ) := by
        simp only [A, map_sub]
        first
          | linear_combination (norm := abel1) h2 - h3 - h1
          | linear_combination (norm := abel1) h2 - h3 + h1
          | linear_combination (norm := abel1) h1 + h2 - h3
          | linear_combination (norm := abel1) -h1 - h2 + h3
      rw [← hr, inner]
      simp only [map_sub, map_add (f := _)]
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) ku - kv

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsAcyclicOfTwoSectionsRetractionStatement

section

@[expose] public section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction : ∀ (C : Type 1) [Category.{0} C] (M : Coef C) (S : C ⥤ C) (u v : 𝟭 C ⟶ S) (r : ∀ T, M.obj (S.obj T) →+ M.obj T), (∀ (T T' : C) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x)) → (∀ T x, r T (M.map (u.app T) x) = 0) → (∀ T x, r T (M.map (v.app T) x) = x) → M.Ac0 ∧ M.Ac1 ∧ M.Ac2 := by
  first | exact @GlobalTheory.coef_acyclic_of_two_sections | exact GlobalTheory.coef_acyclic_of_two_sections | (intros; apply GlobalTheory.coef_acyclic_of_two_sections <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalFirstNeighbourhoodRetractionFormsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_diagonal_firstNeighbourhood_retraction_forms : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S) (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T) (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T) (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T), ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧ (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧ ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧ (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧ (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧ (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  first | exact @GlobalTheory.PDForm.Nbhd.exists_retraction | exact GlobalTheory.PDForm.Nbhd.exists_retraction | (intros; apply GlobalTheory.PDForm.Nbhd.exists_retraction <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH1Bijective

section

@[expose] public section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.Cx

theorem fnMap_h1_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (hA0 : K.M1.Ac0)
    (hA1 : K.M1.Ac1) (hB0 : K.M2.Ac0) : Function.Bijective K.fnMap.h1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hc : K.D1 c.1 = 0 := c.2
    rw [CxMap.h1, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨g, hg⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨g, ?_⟩
    have hf : ∀ T T' (φ : T ⟶ T'), c.1.1 T T' φ = g T' - K.M0.map φ (g T) := by
      intro T T' φ
      have := congrArg (fun p => p.1 T T' φ) hg
      exact this.symm
    have h2c : ∀ T T' (φ : T ⟶ T'),
        c.1.2 T' - K.M1.map φ (c.1.2 T) - K.d0 T' (c.1.1 T T' φ) = 0 := by
      intro T T' φ
      have := congrArg (fun p => p.2.1 T T' φ) hc
      simpa [Cx.D1] using this
    have hw := hA0 (fun T => c.1.2 T - K.d0 T (g T)) (by
      intro T T' φ
      have := h2c T T' φ
      rw [hf, map_sub, K.diffZero_natural] at this
      simp only [map_sub]
      rw [← sub_eq_zero, ← this]; abel)
    refine Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_) (funext fun T => ?_)
    · simp [Cx.D0, hf]
    · have := congrFun hw T
      simp only [Pi.zero_apply, sub_eq_zero] at this
      simp [Cx.D0, this]
  · intro y
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hc : (Cx.single K.M0).D1 c.1 = 0 := c.2
    have hδ : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (c.1.1 T T' φ) - c.1.1 T T'' (φ ≫ ψ) + c.1.1 T' T'' ψ = 0 := by
      intro T T' T'' φ ψ
      have := congrArg (fun p => p.1 T T' T'' φ ψ) hc
      simpa [Cx.D1] using this
    obtain ⟨w, hw⟩ := hA1 (fun T T' φ => K.d0 T' (c.1.1 T T' φ)) (by
      intro T T' T'' φ ψ
      have h := congrArg (K.d0 T'') (hδ T T' T'' φ ψ)
      simp only [map_add (f := _), map_sub, map_zero, K.diffZero_natural] at h ⊢
      rw [← sub_eq_zero, ← neg_eq_zero, ← h]; abel)
    have hdw := hB0 (fun T => K.d1 T (w T)) (by
      intro T T' φ
      have h := congrArg (K.d1 T') (hw T T' φ)
      rw [K.diffOne_diffZero, map_sub, K.diffOne_natural] at h
      exact (sub_eq_zero.mp h.symm))
    let z : K.Z1 := ⟨(c.1.1, w), by
      show K.D1 _ = 0
      refine Prod.ext (funext fun T => funext fun T' => funext fun T'' => funext fun φ =>
        funext fun ψ => ?_) (Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_)
        (funext fun T => ?_))
      · simpa [Cx.D1] using hδ T T' T'' φ ψ
      · simp [Cx.D1, hw T T' φ]
      · simpa [Cx.D1] using congrFun hdw T⟩
    refine ⟨QuotientAddGroup.mk z, ?_⟩
    rw [CxMap.h1, QuotientAddGroup.map_mk]
    congr 1
end GlobalTheory.CxCoh.Cx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH1BijectiveStatement

section

@[expose] public section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.forget_positive_h1_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac0 → K.M1.Ac1 → K.M2.Ac0 → Function.Bijective K.fnMap.h1 := by
  first | exact @GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | exact GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | (intros; apply GlobalTheory.CxCoh.Cx.fnMap_h1_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairs

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem fnMap_pullbackBijective12_of_acyclic {C : Type 1} [Category.{0} C] (K : Cx C)
    (h1 : K.M1.Ac0 ∧ K.M1.Ac1 ∧ K.M1.Ac2) (h2 : K.M2.Ac0 ∧ K.M2.Ac1 ∧ K.M2.Ac2) (h3 : K.M3.Ac0 ∧ K.M3.Ac1 ∧ K.M3.Ac2) :
    K.fnMap.PullbackBijectiveDegreesOneTwo :=
  And.intro (GlobalTheory.T.forget_positive_h1_bijective C K h1.1 h1.2.1 h2.1) (GlobalTheory.T.forget_positive_h2_bijective C K h1.2.1 h1.2.2 h2.1 h2.2.1 h3.1)

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem top_le_preimage_of_hom {T T' : Thick κ t} (f : T ⟶ T') (U : Y.Opens) (h : ⊤ ≤ (T.x ≫ i) ⁻¹ᵁ U) :
    ⊤ ≤ (T'.x ≫ i) ⁻¹ᵁ U := by
  intro p _
  rw [← f.pt, Category.assoc]
  exact h (Set.mem_univ ((spMap f.φ₀).base p))

variable (κ t i)

def liftE (S : Thick κ t ⥤ Thick κ t) (u : 𝟭 _ ⟶ S) : EE κ t i ⥤ EE κ t i where
  obj a := ⟨⟨S.obj a.obj.T, a.obj.U, a.obj.hU, top_le_preimage_of_hom (u.app a.obj.T) a.obj.U a.obj.mem⟩, a.property⟩
  map f := ⟨⟨S.map f.hom.1, f.hom.2⟩⟩
  map_id a := ObjectProperty.hom_ext _ (Subtype.ext (S.map_id a.obj.T))
  map_comp f g := ObjectProperty.hom_ext _ (Subtype.ext (S.map_comp f.hom.1 g.hom.1))

def liftT (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S) : 𝟭 (EE κ t i) ⟶ liftE κ t i S u where
  app a := ⟨⟨v.app a.obj.T, le_rfl⟩⟩
  naturality a b f := ObjectProperty.hom_ext _ (Subtype.ext (v.naturality f.hom.1))

variable {κ t i}

theorem acyc_res_pE (M : Coef (Thick κ t)) (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (h : (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x)) ∧
      (∀ T x, r T (M.map (u.app T) x) = 0) ∧ (∀ T x, r T (M.map (v.app T) x) = x)) :
    (M.res (pE κ t i)).Ac0 ∧ (M.res (pE κ t i)).Ac1 ∧ (M.res (pE κ t i)).Ac2 :=
  GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ (M.res (pE κ t i)) (liftE κ t i S u) (liftT κ t i S u u) (liftT κ t i S u v) (fun a ↦ r a.obj.T)
    (fun a b f x ↦ h.1 a.obj.T b.obj.T f.hom.1 x) (fun a x ↦ h.2.1 a.obj.T x) (fun a x ↦ h.2.2 a.obj.T x)

theorem crystalline_forget_forms_bijective_site_and_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i
  obtain ⟨S, u, v, r1, r2, r3, h1, h2, h3a, h3b, h3c⟩ := GlobalTheory.T.exists_diagonal_firstNeighbourhood_retraction_forms R I κ X t
  have h3 := And.intro h3a (And.intro h3b h3c)
  exact ⟨fnMap_pullbackBijective12_of_acyclic _ (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r1 h1.1 h1.2.1 h1.2.2)
      (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r2 h2.1 h2.2.1 h2.2.2) (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r3 h3a h3b h3c),
    fnMap_pullbackBijective12_of_acyclic _ (acyc_res_pE (i := i) _ S u v r1 h1) (acyc_res_pE (i := i) _ S u v r2 h2)
      (acyc_res_pE (i := i) _ S u v r3 h3)⟩

end GlobalTheory.PDForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | exact GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | (intros; apply GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs <;> assumption)
end
end
