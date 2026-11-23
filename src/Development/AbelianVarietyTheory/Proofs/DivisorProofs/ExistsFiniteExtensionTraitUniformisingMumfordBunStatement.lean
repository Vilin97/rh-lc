module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFieldsStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescends
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatchingStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescent
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescendsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_extension_symmetric_bundle_descends : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (A' : PolAV (Sp Ω)) (α : A'.A.left ⟶ A.A.left) (α₂ : (G2 A'.A).left ⟶ (G2 A.A).left), IsGrpPullback A'.A A.A (spMap ga) α → Geo.Tor.IsSquare α α₂ → LBIso (abelian₂ A'.A A'.L) ((abelian₂ A.A A.L).pull α₂) → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (p : pullback A'.A.hom (spMap j) ⟶ A₁.A.left), io.Finite ∧ l.comp io = j.comp ga ∧ IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ Geo.Tor.IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ p ≫ α₁ = pullback.fst _ _ ≫ α ∧ p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l ∧ LBIso (A'.L.pull (pullback.fst A'.A.hom (spMap j))) (A₁.L.pull p) := by
  first | exact @GlobalTheory.SymFinExt.exists_finite_ext | exact GlobalTheory.SymFinExt.exists_finite_ext | (intros; apply GlobalTheory.SymFinExt.exists_finite_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFraction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem transport_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ G _ _ A gen hgen PP hExt K' _ io A₁ α₁ α₁₂ hα hsqα hΛ R₂ _ _ _ ρ i hρ hi G₂ _ _ β β₂ hβ hsqβ
  haveI := hgen
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R₂)).obj G₂) := Functor.isCommMonObj_obj
  obtain ⟨A₂, q, pq, -, mq, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap i.toRingHom) A₁
  have hq : IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q := ⟨pq, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pq.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pq.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mq]; rfl⟩
  have hLq : LBIso A₂.L (A₁.L.pull q) := LBIso.symm ⟨t, ht⟩
  have hsq : jK R₂ ≫ spMap ρ = spMap i.toRingHom ≫ spMap io ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [hi]
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have hgi : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) gen.inv.left := isGrpPullback_of_iso gen.symm
  have gG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hgi.comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gA : IsGrpPullback A₂.A G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)) := hq.comp (hα.comp gG)
  have g₂ : IsGrpPullback ((Over.pullback (jK R₂)).obj G₂) G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (pullback.fst G₂.hom (jK R₂) ≫ β) :=
    ((isGrpPullback_pullback G₂ (jK R₂)).comp hβ).congr hsq rfl
  obtain ⟨e, he, hee⟩ := grpPullback_iso g₂ gA
  haveI := he
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hgh : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have h5 : e.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
    rw [← hee, ← Category.assoc, hei, Category.id_comp]
  refine ⟨A₂, e, q, he, ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩, hq, hLq, h5⟩

  obtain ⟨g₂m, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
    (isGrpPullback_pullback G (jK R))
  obtain ⟨γ₁, hsqγ, Ha⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) A.A _ hgi
  obtain ⟨q₂, hsqq, Hc⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₁.A A₂.A _ hq
  obtain ⟨e₂, hsqe, Hd⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₂.A ((Over.pullback (jK R₂)).obj G₂) _
    (isGrpPullback_of_iso e)
  have hLK := pull_isLB A.isLB gen.hom.left
  have i₀ : LBIso A.L ((A.L.pull gen.hom.left).pull gen.inv.left) :=
    LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl)
      (chartPullLinComb A.L gen.hom.left (fun _ => gen.inv.left) (fun _ => 𝟙 _) _ (𝟙 _)
        (fun _ => by rw [hgh, Category.id_comp]))
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB (𝟙 _)))
  have Ha' := Ha _ _ _ PP g₂m hLK A.isLB hExt.1 i₀ (hExt.2 g₂m hg₂)
  have Hb : LBIso (abelian₂ A₁.A A₁.L) (PP.pull (α₁₂ ≫ γ₁ ≫ g₂m)) :=
    LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB (DVR.linComb_isLB _ A.isLB _ _) _)
      (pull_isLB hExt.1 _) hΛ
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ α₁₂ α₁₂ rfl)
        (chartPullSame PP (fun _ => α₁₂ ≫ γ₁ ≫ g₂m) (fun _ => γ₁ ≫ g₂m) _ α₁₂ fun _ => rfl) Ha')
  have Hc' := Hc _ _ _ PP _ A₁.isLB A₂.isLB hExt.1 hLq Hb
  have Hd' := Hd _ _ _ PP _ A₂.isLB (pull_isLB A₂.isLB _) hExt.1
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A₂.isLB _)) Hc'
  have E : e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      simp only [Category.assoc, hg₂.1, reassoc_of% hsqγ.1, reassoc_of% hsqα.1, reassoc_of% hsqq.1,
        reassoc_of% hsqe.1, hsqβ.1, reassoc_of% hκ₂.1, hee]
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      simp only [Category.assoc, hg₂.2, reassoc_of% hsqγ.2, reassoc_of% hsqα.2, reassoc_of% hsqq.2,
        reassoc_of% hsqe.2, hsqβ.2, reassoc_of% hκ₂.2, hee]
  exact LBIso.trans (DVR.linComb_isLB _ (pull_isLB A₂.isLB _) _ _) (pull_isLB hExt.1 _)
    (pull_isLB (pull_isLB hExt.1 β₂) κ₂) Hd'
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => E) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFractionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  first | exact @GlobalTheory.Mum.transport_extLam | exact GlobalTheory.Mum.transport_extLam | (intros; apply GlobalTheory.Mum.transport_extLam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisation_bundle_genericFibre_descent : ∀ (R W R₂ W₂ K' Ω' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] [Field K'] [Field Ω'] (φ : R →+* W) (ρ : R →+* R₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (io : FractionRing R →+* K') (j : FractionRing W →+* Ω') (l : K' →+* Ω') (i : K' ≃+* FractionRing R₂) (j₂ : FractionRing W₂ →+* Ω'), Function.Injective φ → Function.Injective ρ → Function.Injective σ → Function.Injective φ₂ → φ₂.comp ρ = σ.comp φ → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) → (∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r))) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (α : AW.A.left ⟶ A.A.left), IsGrpPullback GW G (spMap φ) βW → UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (p : pullback AW.A.hom (spMap j) ⟶ A₁.A.left), IsGrpPullback A₁.A A.A (spMap io) α₁ → p ≫ α₁ = pullback.fst _ _ ≫ α → p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l → LBIso (AW.L.pull (pullback.fst AW.A.hom (spMap j))) (A₁.L.pull p) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsGrpPullback G₂ G (spMap ρ) β → IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q → LBIso A₂.L (A₁.L.pull q) → gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (GW' : Over (Sp W₂)) [GrpObj GW'] [IsCommMonObj GW'] (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' → IsGrpPullback GW' GW (spMap σ) τ → βW' ≫ β = τ ≫ βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.unif_bundle_generic_descent | exact GlobalTheory.unif_bundle_generic_descent | (intros; apply GlobalTheory.unif_bundle_generic_descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_trait_baseChange : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  intro R R₂ W W₂ _ _ _ _ _ _ _ _ _ _ _ _ ρ φ σ φ₂ _ hW hW₂ hσ hloc hc hφ₂ G _ _ hG G₂ _ _ β hβ GW _ _ βW hβW DW AW UW
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hW.1
  have hWa : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGW : IsSemiAbelian GW := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβW (isGrpPullback_pullback G (spMap φ))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)
  obtain ⟨D₁, hX, A₁, U₁, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hWa hσ.1 σ hσ.2.1 (map_maximalIdeal_le σ) hGW UW
  have hτ : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) GW (spMap σ) (pullback.fst GW.hom (specOf σ)) :=
    isGrpPullback_pullback GW (specOf σ)
  have hb : spMap σ ≫ spMap φ = spMap φ₂ ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  have hn := (hτ.comp hβW).congr hb rfl
  have hw : (pullback.fst GW.hom (specOf σ) ≫ βW) ≫ G.hom =
      (((Over.pullback (specOf σ)).obj GW).hom ≫ spMap φ₂) ≫ spMap ρ := by
    rw [hn.1.w]; exact (Category.assoc _ _ _).symm
  have h₁ := hβ.1.lift_fst _ _ hw
  have h₂ := hβ.1.lift_snd _ _ hw
  have hβ' : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) G₂ (spMap φ₂) (hβ.1.lift _ _ hw) :=
    hβ.cancel (hn.congr rfl h₁.symm) h₂
  have hsq : jK W₂ ≫ spMap φ₂ =
      spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂) ≫ jK R₂ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have cond : (pullback.fst ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫ hβ.1.lift _ _ hw) ≫ G₂.hom =
      (pullback.snd ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫
        spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂)) ≫ jK R₂ := by
    rw [Category.assoc, h₂, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc]
  refine ⟨(Over.pullback (specOf σ)).obj GW, inferInstance, inferInstance, hβ.1.lift _ _ hw,
    pullback.fst GW.hom (specOf σ), D₁, A₁, U₁, pullback.lift _ _ cond, hβ', hτ, h₁, pullback.lift_fst _ _ _, ?_⟩
  obtain ⟨wL, hwL, -⟩ := hP.lg
  exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U₁.LG.L _ _ rfl)
    (chartPullSame UW.LG.L _ (fun _ => (Iso.refl ((Over.pullback (specOf σ)).obj GW)).hom.left ≫
      pullback.fst GW.hom (specOf σ)) _ _ fun _ => by
        exact congrArg (_ ≫ ·) (Category.id_comp _).symm) ⟨wL, hwL⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  first | exact @GlobalTheory.Mum.unif_trait_baseChange | exact GlobalTheory.Mum.unif_trait_baseChange | (intros; apply GlobalTheory.Mum.unif_trait_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBun

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_finExt_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨W, _, _, _, φ, GW, _, _, βW, βW₂, DW, AW, UW, hW, hφi, hφl, hpbW, hsqW, hlamW⟩ :=
    GlobalTheory.T.exists_trait_uniformisation_mumfordBundle R hR G hG A gen hgen PP hPP
  obtain ⟨ga, α, α₂, hga, hpbα, hsqα, hlamα, hcompα⟩ :=
    GlobalTheory.T.generic_uniformised_pullback_mumfordBundle_matching R hR G hG A gen hgen PP hPP W φ GW βW βW₂ DW AW UW hW hφi hφl hpbW hsqW hlamW

  have : CharZero R := hR.2
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, Ω', _, j, l, A₁, α₁, α₁₂, p, hio, hlio, hpb₁, hsq₁, hlam₁, hp₁, hp₂, hpL⟩ :=
    GlobalTheory.T.exists_finite_extension_symmetric_bundle_descends (FractionRing R) (FractionRing W) ga A AW α α₂ hpbα hsqα hlamα
  have hcomp : ∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r)) := by
    intro r
    have h := DFunLike.congr_fun hlio (algebraMap R (FractionRing R) r)
    simp only [RingHom.comp_apply] at h
    rw [h, hga]
  obtain ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hρ, hW₂, hσ, hσl, hφ₂i, hφ₂l, hsq, hi, hj₂, hl₂⟩ :=
    GlobalTheory.T.exists_common_extension_dvr_fraction_fields R W hR hW φ hφi hφl K' Ω' io j l hio hcomp
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ, hρ, ?_⟩
  intro G₂ _ _ β β₂ hpb₂ hsq₂
  obtain ⟨A₂, gen₂, q, hgen₂, hext₂, hpbq, hlamq, hcompq⟩ :=
    GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction R G A gen hgen PP hPP K' io A₁ α₁ α₁₂ hpb₁ hsq₁ hlam₁ R₂ ρ i hρ.2.1 hi G₂ β β₂ hpb₂ hsq₂
  obtain ⟨GW', _, _, βW', τ, DW', AW', UW', κ, hpbW', hpbτ, hβτ, hκ, hLτ⟩ :=
    GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext R R₂ W W₂ ρ φ σ φ₂ hR hW hW₂ hσ hσl hsq hφ₂i G hG G₂ β hpb₂ GW βW hpbW DW AW UW
  refine ⟨A₂, gen₂, W₂, inferInstance, inferInstance, inferInstance, φ₂, GW', inferInstance, inferInstance,
    βW', DW', AW', UW', κ, hgen₂, hext₂, hW₂, hφ₂i, hφ₂l, hpbW', hκ, ?_⟩
  exact GlobalTheory.T.uniformisation_bundle_genericFibre_descent R W R₂ W₂ K' Ω' φ ρ σ φ₂ io j l i j₂ hφi hρ.2.1 hσ.2.1 hφ₂i hsq hcomp hi hj₂ hl₂
    G A gen GW βW DW AW UW α hpbW hcompα A₁ α₁ p hpb₁ hp₁ hp₂ hpL G₂ β A₂ gen₂ q hpb₂ hpbq hlamq hcompq
    GW' βW' τ DW' AW' UW' κ hpbW' hpbτ hβτ hκ hLτ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBunStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExtension_trait_uniformisingMumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.Mum.exists_finExt_trait_unif_lam | exact GlobalTheory.Mum.exists_finExt_trait_unif_lam | (intros; apply GlobalTheory.Mum.exists_finExt_trait_unif_lam <;> assumption)
end
end
