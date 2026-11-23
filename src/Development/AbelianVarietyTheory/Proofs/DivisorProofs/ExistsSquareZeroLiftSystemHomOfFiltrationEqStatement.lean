module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefectStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstantsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystemsStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectedLocIsoOfDefectCoboundary

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_corr_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S S' Φ θ hθ E hEI hEs hEd

  have hext : ∀ U : AffOp X₀, ∃! η : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj U,
      (∀ b w, η (S.p U b • w) = (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) b * η w) ∧
      (∀ w, η w ∈ I.map (algebraMap R (S'.F.obj U))) ∧ ∀ w : GlobForm s₀, η (w.1 U) = E w U := fun U ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj U) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ((Pi.evalAddMonoidHom _ U).comp E)
      (fun r w ↦ by simp [hEs]) (fun w ↦ hEI w U)

  choose η hη using fun U ↦ (hext U).exists
  have hψ : ∀ U : AffOp X₀, ∃ ψ : S.F.obj U →ₐ[R] S'.F.obj U,
      IsTheta I (S.p U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ψ (-η U) := fun U ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj U) I hI π hπ (S.p U) (S.semi U) (S.surj U)
      (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)).2 (-η U)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hη U).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hη U).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ U b, ψ U b = Φ.φ U b + η U (D R₀ (Sec s₀ U.unop.1) (S.p U b)) := fun U b ↦ by
    have h := (hψ U).der b
    rw [AddMonoidHom.neg_apply] at h
    change -η U _ = Φ.φ U b - ψ U b at h
    linear_combination h
  refine ⟨ψ, fun U b ↦ ?_, fun U V a b ↦ ?_⟩
  · rw [hψv, map_add (f := _), Φ.red, (S'.ker U _).2 ((hη U).2.1 _), add_zero]
  ·
    let α : S.F.obj U →ₐ[R] S'.F.obj V := (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)
    let χ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V := θ U V a + (mp S'.F a).toAddMonoidHom.comp (η U) -
      (η V).comp (p1 (OAff s₀) a).toAddMonoidHom
    have hχ : ∀ w, χ w = θ U V a w + mp S'.F a (η U w) - η V (p1 (OAff s₀) a w) := fun _ ↦ rfl

    have hmemV : ∀ w, η V w ∈ I.map (algebraMap R (S'.F.obj V)) := (hη V).2.1
    have hdiff : ∀ c : S.F.obj U, ∀ x ∈ I.map (algebraMap R (S'.F.obj V)),
        (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) * x = α c * x := by
      intro c x hx
      have h1 := (hθ U V a).der c
      have h2 : α c - (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) ∈ I.map (algebraMap R (S'.F.obj V)) :=
        h1 ▸ (hθ U V a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj V) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hθ U V a).smul, (hη U).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← S.nat a b, (hη V).1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hθ U V a).mem w) (algHom_mem_map I _ ((hη U).2.1 w))) (hmemV _)
      · rw [hχ, hEd, amitsur_d0_apply, (hη U).2.2, ← w.2 a, (hη V).2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ U.unop.1) (S.p U b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) a (S.p U b) = S.p V (mp S.F a b) := (S.nat a b).symm
    rw [hn] at h0
    have h1 := (hθ U V a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add (f := _)]
    simp only [AlgEquiv.coe_toAlgHom] at h0 h1 ⊢
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectedLocIsoOfDefectCoboundaryStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_corrected_locIso_of_defect_coboundary : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  first | exact @GlobalTheory.LiftSys.exists_corr_of_defect | exact GlobalTheory.LiftSys.exists_corr_of_defect | (intros; apply GlobalTheory.LiftSys.exists_corr_of_defect <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSystemDefectCocycleGlobalForms

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Defect

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S S' : Sys I π s₀} (Φ : S.LocIso S')

abbrev al {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)

abbrev be {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)

theorem map_mem {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (f : B →ₐ[R] B')
    {x : B} (hx : x ∈ I.map (algebraMap R B)) : f x ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (f : B →+* B') hx
  rwa [Ideal.map_map, f.comp_algebraMap] at h

theorem mul_eq_zero' (hI : I ^ 2 = 0) {B : Type} [CommRing B] [Algebra R B] {x y : B}
    (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B] at h
  simpa using h

theorem diff_mem {U V : AffOp X₀} (a : U ⟶ V) (b : S.F.obj U) :
    al Φ a b - be Φ a b ∈ I.map (algebraMap R (S'.F.obj V)) := by
  rw [← S'.ker V, map_sub, sub_eq_zero]
  change S'.p V (mp S'.F a (Φ.φ U b)) = S'.p V (Φ.φ V (mp S.F a b))
  rw [S'.nat, Φ.red, Φ.red, S.nat]

theorem ex (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) :
    ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V, IsTheta I (S.p U) (al Φ a) (be Φ a) θ :=
  (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U) (S.semi U)
    (S.surj U) (S.ker U) (al Φ a)).1 (be Φ a) (diff_mem Φ a)

def th (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V :=
  (ex Φ hI hπ a).exists.choose

theorem th_spec (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : IsTheta I (S.p U) (al Φ a) (be Φ a) (th Φ hI hπ a) :=
  (ex Φ hI hπ a).exists.choose_spec

theorem th_comp (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V W : AffOp X₀} (a : U ⟶ V)
    (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]) :
    th Φ hI hπ (a ≫ b) x = mp S'.F b (th Φ hI hπ a x) + th Φ hI hπ b (p1 (OAff s₀) a x) := by
  let θ' : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj W :=
    ((mp S'.F b).toRingHom.toAddMonoidHom.comp (th Φ hI hπ a)) +
      (th Φ hI hπ b).comp (p1 (OAff s₀) a).toAddMonoidHom
  have hA := th_spec Φ hI hπ a
  have hB := th_spec Φ hI hπ b
  have h : IsTheta I (S.p U) (al Φ (a ≫ b)) (be Φ (a ≫ b)) θ' := by
    refine ⟨fun c w ↦ ?_, fun c ↦ ?_, fun w ↦ ?_⟩
    · change mp S'.F b (th Φ hI hπ a (S.p U c • w)) + th Φ hI hπ b (p1 (OAff s₀) a (S.p U c • w)) =
        al Φ (a ≫ b) c * (mp S'.F b (th Φ hI hπ a w) + th Φ hI hπ b (p1 (OAff s₀) a w))
      rw [hA.smul, oneFormsMapOfFunctorMorphism_smul]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.smul, map_mul]
      have hz : (mp S'.F b (al Φ a c) - al Φ b (mp S.F a c)) * th Φ hI hπ b (p1 (OAff s₀) a w) = 0 := by
        refine mul_eq_zero' hI ?_ (hB.mem _)
        have : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
        rw [this, ← map_sub]
        exact map_mem _ (diff_mem Φ a c)
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      rw [e2]
      linear_combination -hz
    · change mp S'.F b (th Φ hI hπ a (D R₀ _ (S.p U c))) + th Φ hI hπ b (p1 (OAff s₀) a (D R₀ _ (S.p U c))) =
        al Φ (a ≫ b) c - be Φ (a ≫ b) c
      rw [hA.der, p1_D]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.der, map_sub]
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      have e3 : be Φ (a ≫ b) c = be Φ b (mp S.F a c) := by
        change Φ.φ W (mp S.F (a ≫ b) c) = Φ.φ W (mp S.F b (mp S.F a c)); rw [mp_comp]
      have e4 : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
      rw [e2, e3, e4]; ring
    · exact Ideal.add_mem _ (map_mem _ (hA.mem w)) (hB.mem _)
  have := (ex Φ hI hπ (a ≫ b)).unique (th_spec Φ hI hπ (a ≫ b)) h
  exact DFunLike.congr_fun this x

def cocyc (hI : I ^ 2 = 0) (hπ : Function.Surjective π) : GlobForm s₀ →+ Z1 S'.F where
  toFun w := ⟨fun U V a ↦ th Φ hI hπ a (w.1 U), fun U V W a b ↦ by
    change th Φ hI hπ (a ≫ b) (w.1 U) = mp S'.F b (th Φ hI hπ a (w.1 U)) + th Φ hI hπ b (w.1 V)
    rw [th_comp, w.2 a]⟩
  map_zero' := Subtype.ext (by funext U V a; exact map_zero _)
  map_add' w w' := Subtype.ext (by funext U V a; exact map_add _ _ _)

theorem th_smul (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) (r : R)
    (x : Ω[Sec s₀ U.unop.1⁄R₀]) : th Φ hI hπ a (π r • x) = r • th Φ hI hπ a x := by
  rw [← algebraMap_smul (Sec s₀ U.unop.1) (π r) x, ← (S.semi U).map_algebraMap, (th_spec Φ hI hπ a).smul,
    AlgHom.commutes, ← Algebra.smul_def]

end GlobalTheory.LiftSys.Defect

theorem GlobalTheory.LiftSys.exists_defect_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  intro R R₀ _ _ I hI π hπ _ X₀ s₀ S S' Φ
  refine ⟨fun U V a ↦ Defect.th Φ hI hπ a, Defect.cocyc Φ hI hπ, fun U V a ↦ Defect.th_spec Φ hI hπ a,
    fun w U V a ↦ rfl, fun w U V a ↦ (Defect.th_spec Φ hI hπ a).mem _, fun r w ↦ ?_⟩
  refine Subtype.ext ?_
  funext U V a
  exact Defect.th_smul Φ hI hπ a r (w.1 U)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSystemDefectCocycleGlobalFormsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_liftSystemDefect_cocycle_globalForms : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  first | exact @GlobalTheory.LiftSys.exists_defect_cocycle | exact GlobalTheory.LiftSys.exists_defect_cocycle | (intros; apply GlobalTheory.LiftSys.exists_defect_cocycle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemHomOfFiltrationEq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem sysHom_of_K_eq : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S S' : Sys I π s₀, S.Full hI → S.K hI = S'.K hI → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S S' hF hK
  obtain ⟨Φ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S S'
  obtain ⟨θ, v, hθ, hv, hvI, hvs⟩ := GlobalTheory.T.exists_liftSystemDefect_cocycle_globalForms R R₀ I hI π hπ hk X₀ s₀ S S' Φ

  have hcl : ∀ w, H1.mk _ (v w) = 0 := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c', hc'⟩ := hρ.1 (Form.cl s₀ f)
    have hmem : c' ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S hρ hF c').2 (by rw [hc', hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
    have hρz : rho hI hk s₀ z = 0 := (hρ.2 z).2 hz
    have hfo : FormOf hI hk y w := ⟨f, by rw [← hc', map_add (f := _), hρz, add_zero], hf⟩
    have hm := GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S S' Φ θ hθ y hy w hfo (v w) (hv w)
    have hy' : y ∈ S'.K hI := hK ▸ hy
    have h0 : S'.r hI y = 0 := hy'
    rw [h0] at hm
    exact neg_eq_zero.1 hm.symm

  let W : Submodule R (C0 S'.F) :=
    { carrier := {g | S'.IsIdealValuedLiftSystemCochain g}
      add_mem' := fun {g g'} hg hg' U ↦ Ideal.add_mem _ (hg U) (hg' U)
      zero_mem' := fun U ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg U ↦ by
        show r • g U ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hg U) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext U
    show r • m U = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj U)) hrI) (hm U)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  have hq : ∀ w, ∃ m ∈ W, d0 S'.F m = ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro w
    obtain ⟨g, hgI, hg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hG.const S' (v w) (hvI w) (hcl w)
    exact ⟨g, hgI, hg⟩
  have hv' : ∀ (r : R) w, ((Z1 S'.F).subtype.toAddMonoidHom.comp v) (π r • w) =
      r • ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro r w
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, hvs]
    rfl
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj
    (C0 S'.F) (C1 S'.F) W hW (d0 S'.F) _ hv' hq
  exact GlobalTheory.T.exists_corrected_locIso_of_defect_coboundary R R₀ I hI π hπ hk X₀ s₀ hG.par S S' Φ θ hθ u hu2 hu1 (fun w U V a ↦
    (hv w U V a).symm.trans (congrFun (congrFun (congrFun (hu3 w) U) V) a).symm)

end GlobalTheory.LiftSys
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemHomOfFiltrationEqStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_squareZeroLiftSystem_hom_of_filtration_eq : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S S' : Sys I π s₀, S.Full hI → S.K hI = S'.K hI → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  first | exact @GlobalTheory.LiftSys.sysHom_of_K_eq | exact GlobalTheory.LiftSys.sysHom_of_K_eq | (intros; apply GlobalTheory.LiftSys.sysHom_of_K_eq <;> assumption)
end
end
