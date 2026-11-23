module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUnique
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalLiftOfDefectCoboundary

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_natLift_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar C' _ F' L L' n l hl κ u hκ hus hum hκd
  have hext : ∀ T : C', ∃! ξ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T,
      (∀ b w, ξ (L.p (n.G.obj T) b • w) = l T b * ξ w) ∧
      (∀ w, ξ w ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ w : GlobForm s₀, ξ (w.1 (n.G.obj T)) = u w T := fun T ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T) ((Pi.evalAddMonoidHom _ T).comp u)
      (fun r w ↦ by simp [hus]) (fun w ↦ hum w T)
  choose ξ hξ using fun T ↦ (hext T).exists
  have hψ : ∀ T : C', ∃ ψ : L.B (n.G.obj T) →ₐ[R] L'.B T,
      IsTheta I (L.p (n.G.obj T)) (l T) ψ (-ξ T) := fun T ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (L.B (n.G.obj T)) (Sec s₀ (n.G.obj T).unop.1) (L'.B T) I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T)).2 (-ξ T)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hξ T).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hξ T).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ T b, ψ T b = l T b + ξ T (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) := fun T b ↦ by
    have h := (hψ T).der b
    rw [AddMonoidHom.neg_apply] at h
    change -ξ T _ = l T b - ψ T b at h
    linear_combination h
  refine ⟨ψ, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · rw [hψv, map_add (f := _), hl, (L'.ker T _).2 ((hξ T).2.1 _), add_zero]
  · let α : L.B (n.G.obj T) →ₐ[R] L'.B T' := (L'.ρ a).comp (l T)
    let χ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T' := κ T T' a + (L'.ρ a).toAddMonoidHom.comp (ξ T) -
      (ξ T').comp (p1 (OAff s₀) (n.G.map a)).toAddMonoidHom
    have hχ : ∀ w, χ w = κ T T' a w + L'.ρ a (ξ T w) - ξ T' (p1 (OAff s₀) (n.G.map a) w) := fun _ ↦ rfl
    have hmemV : ∀ w, ξ T' w ∈ I.map (algebraMap R (L'.B T')) := (hξ T').2.1
    have hdiff : ∀ c : L.B (n.G.obj T), ∀ x ∈ I.map (algebraMap R (L'.B T')),
        l T' (L.ρ (n.G.map a) c) * x = α c * x := by
      intro c x hx
      have h1 := (hκ T T' a).der c
      have h2 : α c - l T' (L.ρ (n.G.map a) c) ∈ I.map (algebraMap R (L'.B T')) :=
        h1 ▸ (hκ T T' a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T') (L.p _)
      (L.semi _) (L.surj _) (L.ker _) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hκ T T' a).smul, (hξ T).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← L.nat (n.G.map a) b, (hξ T').1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hκ T T' a).mem w) (algHom_mem_map I _ ((hξ T).2.1 w))) (hmemV _)
      · rw [hχ, hκd, (hξ T).2.2, ← w.2 (n.G.map a), (hξ T').2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) (n.G.map a) (L.p _ b) = L.p _ (L.ρ (n.G.map a) b) := (L.nat (n.G.map a) b).symm
    rw [hn] at h0
    have h1 := (hκ T T' a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add (f := _)]
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalLiftOfDefectCoboundaryStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_naturalLift_of_defect_coboundary : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  first | exact @GlobalTheory.LiftSys.exists_natLift_of_defect | exact GlobalTheory.LiftSys.exists_natLift_of_defect | (intros; apply GlobalTheory.LiftSys.exists_natLift_of_defect <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearCochainOfDegreeOneObstructionZer

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_cochain_of_isOb1_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hP C' _ F' L L' n l h
  obtain ⟨κ, -, -, hκ, -, -, -⟩ := h 0
  let W : Submodule R (∀ T : C', L'.B T) :=
    { carrier := {m | ∀ T, m T ∈ I.map (algebraMap R (L'.B T))}
      add_mem' := fun {m m'} hm hm' T ↦ Ideal.add_mem _ (hm T) (hm' T)
      zero_mem' := fun T ↦ Ideal.zero_mem _
      smul_mem' := fun r m hm T ↦ by
        show r • m T ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hm T) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext T
    show r • m T = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (L'.B T)) hrI) (hm T)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  let q : (∀ T : C', L'.B T) →ₗ[R] (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun m T T' a ↦ m T' - L'.ρ a (m T)
      map_add' := fun m m' ↦ by funext T T' a; simp only [Pi.add_apply, map_add (f := _)]; abel
      map_smul' := fun r m ↦ by
        funext T T' a; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply] }
  let v : GlobForm s₀ →+ (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun w T T' a ↦ κ T T' a (w.1 (n.G.obj T))
      map_zero' := by funext T T' a; exact map_zero (κ T T' a)
      map_add' := fun w w' ↦ by funext T T' a; exact map_add (κ T T' a) _ _ }
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    funext T T' a
    show κ T T' a (π r • w.1 (n.G.obj T)) = r • κ T T' a (w.1 (n.G.obj T))
    have hp : L.p (n.G.obj T) (algebraMap R (L.B (n.G.obj T)) r) = algebraMap R₀ _ (π r) := by
      have h1 := L.semi (n.G.obj T) r 1
      rw [← Algebra.algebraMap_eq_smul_one, map_one] at h1
      rw [h1, Algebra.algebraMap_eq_smul_one]
    have h3 := (hκ T T' a).smul (algebraMap R _ r) (w.1 (n.G.obj T))
    rw [hp, algebraMap_smul, AlgHom.commutes] at h3
    rw [h3, Algebra.smul_def]
  have hq : ∀ w, ∃ m ∈ W, q m = v w := by
    intro w
    obtain ⟨κw, σw, zw, hκw, hσw, hc, hz⟩ := h w
    obtain ⟨f, hf⟩ := H1.mk_eq_zero.1 hc.symm
    have hκκ : ∀ T T' (a : T ⟶ T'), κ T T' a = κw T T' a := fun T T' a ↦
      (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L'.B T') _ _ ((l T').comp (L.ρ (n.G.map a))) _ _
        (hκ T T' a)).2.2.1 (hκw T T' a)
    refine ⟨fun T ↦ σw T (f T), fun T ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T)
      (L'.ker T) (σw T) (hσw T)).1 (f T), ?_⟩
    funext T T' a
    have hn := (sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) _ _ (L'.p T')
      (L'.semi T') (L'.surj T') (L'.ker T') (L'.ρ a) (mp F' a) (L'.nat a) (σw T) (σw T') (hσw T) (hσw T')).1 (f T)
    have hzf : zw.1 T T' a = f T' - extHom R₁ (mp F' a) (f T) := by
      rw [← hf]; rfl
    show σw T' (f T') - L'.ρ a (σw T (f T)) = κ T T' a (w.1 (n.G.obj T))
    rw [hκκ, ← (hz T T' a).2, hzf, map_sub, hn]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hP _ _ W hW q v hv hq
  exact ⟨κ, u, hκ, hu1, hu2, fun w T T' a ↦ (congrFun (congrFun (congrFun (hu3 w) T) T') a).symm⟩

end GlobalTheory.Obs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearCochainOfDegreeOneObstructionZerStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semilinear_cochain_of_degreeOneObstruction_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  first | exact @GlobalTheory.Obs.exists_cochain_of_isOb1_zero | exact GlobalTheory.Obs.exists_cochain_of_isOb1_zero | (intros; apply GlobalTheory.Obs.exists_cochain_of_isOb1_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsNaturalOfObstructionOneZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem exists_natural_lift_of_ob1_eq_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → (∀ w, L.IsOb1 L' n l α w 0) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hpar hproj C' _ F' L L' n l hl h0
  obtain ⟨κ, u, hκ, hu, huI, hd⟩ := GlobalTheory.T.exists_semilinear_cochain_of_degreeOneObstruction_zero R R₀ I hI π hπ hk R₁ α X₀ s₀ hproj C' F' L L' n l h0
  exact GlobalTheory.T.exists_naturalLift_of_defect_coboundary R R₀ I hI π hπ hk X₀ s₀ hpar C' F' L L' n l hl κ u hκ hu huI hd

end GlobalTheory.Obs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsNaturalOfObstructionOneZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lifts_natural_of_obstructionOne_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → (∀ w, L.IsOb1 L' n l α w 0) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  first | exact @GlobalTheory.Obs.exists_natural_lift_of_ob1_eq_zero | exact GlobalTheory.Obs.exists_natural_lift_of_ob1_eq_zero | (intros; apply GlobalTheory.Obs.exists_natural_lift_of_ob1_eq_zero <;> assumption)
end
end
