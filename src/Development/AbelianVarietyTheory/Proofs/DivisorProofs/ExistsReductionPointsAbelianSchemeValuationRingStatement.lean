module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquiv
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLocal

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_theta_local {S : Scheme.{0}} (G : Over S) [GrpObj G] (hA : IsAbelianScheme G)
    (L : LB G.left) (hL : L.IsLB) (U : Type) [CommRing U] [IsLocalRing U] (u : Sp U ⟶ S) (n : ℕ)
    (x : Over.mk u ⟶ G) (hx : x ^ n = 1) : ∃ θ : ThetaGrp G L (n : ℤ) (Over.mk u), θ.pt = x := by
  have := hA.comm
  set a : Over.mk u ⊗ G ⟶ G := fst (Over.mk u) G ≫ x with ha
  set y : Over.mk u ⊗ G ⟶ G := snd (Over.mk u) G with hy
  have cube := GlobalTheory.CubeTop.cubeTheorem S G hA L hL (Over.mk u ⊗ G)
  have key : ∀ m : ℕ, ∃ t : LB.Gen (LB.LinComb L
      ![(a ^ m * y).left, (a ^ m).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left]
      ![1, -1, -(m : ℤ), (m : ℤ), (m : ℤ) - 1, 1 - (m : ℤ)]), t.IsGen := by
    intro m
    induction m with
    | zero =>
      obtain ⟨t, ht⟩ := cube 1 a y
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ 0 * y).left, (a ^ 0).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ) - 1, 1 - ((0 : ℕ) : ℤ)]) (fun V _ g => by
          simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
            Matrix.cons_val_one, pow_zero, _root_.one_mul]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module) t ht
      exact ⟨t', ht'⟩
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨c, hc⟩ := cube (a ^ m) a y
      have e₁ : a ^ m * a * y = a ^ (m + 1) * y := by rw [pow_succ]
      have e₂ : a ^ m * a = a ^ (m + 1) := by rw [pow_succ]
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ (m + 1) * y).left, (a ^ (m + 1)).left, (a * y).left, a.left, y.left,
          (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ) - 1, 1 - ((m + 1 : ℕ) : ℤ)])
        (fun V _ g => by
          rw [Fintype.prod_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Matrix.cons_val_one, e₁, e₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module)
        (LB.mulGen L _ _ _ _ t c) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hc)
      exact ⟨t', ht'⟩
  obtain ⟨t, ht⟩ := key n
  have han : a ^ n = 1 := by rw [ha, ← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := U) L hL (K := Fin 2)
    ![x.left, (1 : Over.mk u ⟶ G).left] ![-(n : ℤ), n]
  have h1 : (fst (Over.mk u) G).left ≫ (1 : Over.mk u ⟶ G).left = (1 : Over.mk u ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk u) G).left ≫ x.left = a.left := rfl
  have h3 : translPt G x = a * y := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (Over.mk u) G).left, (translPt G x).left]) (ε' := ![(n : ℤ), -(n : ℤ)]) (fun V _ g => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, han, h1, h2, h3, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ e (fst (Over.mk u) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.WeilSpecialise

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem unitOn_surjective {R : Type} [CommRing R] : Function.Surjective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective.2

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_specialise : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (Lb : LB G.left), Lb.IsLB → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ (P Q : Over.mk u ⟶ G) (c : Uˣ), P ^ n = 1 → Q ^ n = 1 → ∀ (P' Q' : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), P'.left = spMap (algebraMap U Ω) ≫ P.left → Q'.left = spMap (algebraMap U Ω) ≫ Q.left → Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → ∀ (k : Type) [Field k] (h : U →+* k) (P₀ Q₀ : Over.mk (spMap h ≫ u) ⟶ G), P₀.left = spMap h ≫ P.left → Q₀.left = spMap h ≫ Q.left → Out.WeilIs G Lb n P₀ Q₀ (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω _ _ _ _ _ _ S G _ hA Lb hLb u n _ P Q c hP hQ P' Q' hP' hQ' HΩ k _ h P₀ Q₀ hP₀ hQ₀
  have hG := globalFns_holds
  have loc : ∀ z : Over.mk u ⟶ G, z ^ n = 1 → ∀ p : (Over.mk u).left, ∃ V : (Over.mk u).left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp G Lb (n : ℤ) (overRes V), θ.pt = overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_local G hA Lb hLb U u n z hz
    obtain ⟨θ', h'⟩ := GlobalTheory.CommutatorPairing.exists_pull hLb θ (overResι (⊤ : (Over.mk u).left.Opens))
    exact ⟨⊤, trivial, θ', h'.trans (by rw [hθ])⟩
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hLb (loc P hP) (loc Q hQ)
  obtain ⟨c₁, rfl⟩ := unitOn_surjective c₀
  let iΩ : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ Over.mk u := Over.homMk (spMap (algebraMap U Ω)) rfl
  have eP : P' = iΩ ≫ P := Over.OverMorphism.ext hP'
  have eQ : Q' = iΩ ≫ Q := Over.OverMorphism.ext hQ'
  have H₁ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb iΩ hc₀
  rw [← eP, ← eQ] at H₁
  have H₁' : Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω).toMonoidHom c₁)) := by
    rw [← map_unitOn]; exact H₁
  have e := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLb H₁' HΩ
  have e' := unitOn_inj e
  have hc : c₁ = c := Units.ext (IsFractionRing.injective U Ω (congrArg Units.val e'))
  subst hc
  let ik : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  have eP₀ : P₀ = ik ≫ P := Over.OverMorphism.ext hP₀
  have eQ₀ : Q₀ = ik ≫ Q := Over.OverMorphism.ext hQ₀
  have H₂ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb ik hc₀
  rw [← eP₀, ← eQ₀] at H₂
  have := map_unitOn h c₁
  exact this ▸ H₂

end GlobalTheory.WeilSpecialise
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosed

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionLiftVal

theorem sections_restrict_bijective (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k)
    {X : Scheme.{0}} (p : X ⟶ Sp U) [IsFinite p] [Etale p] :
    Function.Bijective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
  have inj : Function.Injective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
    rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ e
    have e' : spMap h ≫ s₁ = spMap h ≫ s₂ := congrArg Subtype.val e
    haveI : LocallyOfFiniteType (Over.mk p).hom := inferInstanceAs (LocallyOfFiniteType p)
    haveI : FormallyUnramified (Over.mk p).hom := inferInstanceAs (FormallyUnramified p)
    haveI : IsSeparated (Over.mk p).hom := inferInstanceAs (IsSeparated p)
    let f₁ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₁ h₁
    let f₂ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₂ h₂
    have hr := (FinEt.comp_eq_comp_iff_range f₁ f₂ (spMap h)).1 e'
    haveI : PreconnectedSpace (Over.mk (𝟙 (Sp U))).left := inferInstanceAs (PreconnectedSpace (Sp U))
    have hc : IsClopen (Set.range (FinEt.agreeι f₁ f₂)) :=
      ⟨(FinEt.agreeι f₁ f₂).isClosedEmbedding.isClosed_range, (FinEt.agreeι f₁ f₂).isOpenEmbedding.isOpen_range⟩
    obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
    have hu : Set.range (FinEt.agreeι f₁ f₂) = Set.univ := hc.eq_univ ⟨_, hr ⟨z, rfl⟩⟩
    have := (FinEt.comp_eq_comp_iff_range f₁ f₂ (𝟙 _)).2 (by rw [hu]; exact Set.subset_univ _)
    apply Subtype.ext
    simpa [f₁, f₂] using this
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨hBfin, hB⟩ := FinEt.card_points_eq_finrank p (spMap h) z
  obtain ⟨-, hC⟩ := FinEt.card_points_eq_finrank p (spMap (algebraMap U Ω)) w
  haveI := hBfin
  haveI : Finite {s : Sp U ⟶ X // s ≫ p = 𝟙 _} := Finite.of_injective _ inj
  have hv : ValuativeCriterion p := by
    have hp : IsProper p := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let r : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} → {x : Sp Ω ⟶ X // x ≫ p = spMap (algebraMap U Ω)} :=
    fun s => ⟨spMap (algebraMap U Ω) ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩
  have hrs : Function.Surjective r := by
    rintro ⟨x, hx⟩
    let Q : ValuativeCommSq p :=
      { R := U, K := Ω, i₁ := x, i₂ := 𝟙 _, commSq := ⟨hx.trans (Category.comp_id _).symm⟩ }
    obtain ⟨W⟩ := hv Q
    exact ⟨⟨W.default.l, W.default.fac_right⟩, Subtype.ext W.default.fac_left⟩
  have hle := Nat.card_le_card_of_surjective r hrs
  have hrank := (Scheme.Hom.isLocallyConstant_finrank p).apply_eq_of_preconnectedSpace (spMap h z)
    (spMap (algebraMap U Ω) w)
  refine inj.bijective_of_nat_card_le ?_
  rw [hB, hrank, ← hC]
  exact hle

theorem torsion_lift_unique : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ y : Over.mk (spMap h ≫ u) ⟶ G, y ^ n = 1 → ∃! P : Over.mk u ⟶ G, P ^ n = 1 ∧ y.left = spMap h ≫ P.left := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u n hn y hy
  letI : GrpObj ((Over.pullback u).obj G) := Functor.grpObjObj
  have hgp : IsGrpPullback ((Over.pullback u).obj G) G u (pullback.fst G.hom u) := isGrpPullback_pullback G u
  haveI : IsAbelianScheme ((Over.pullback u).obj G) := GlobalTheory.isAbelianScheme_pullback_obj u G hA
  have hnU : IsUnit (n : Γ(Sp U, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion ((Over.pullback u).obj G) hnU
  have key : ∀ {X : Scheme.{0}} (t : X ⟶ Sp U) (b : X ⟶ S), b = t ≫ u →
      ∃ Φ : (Over.mk t ⟶ torsion ((Over.pullback u).obj G) n) → (Over.mk b ⟶ G),
        Function.Injective Φ ∧ (∀ a, Φ a ^ n = 1) ∧ (∀ w : Over.mk b ⟶ G, w ^ n = 1 → ∃ a, Φ a = w) ∧
        ∀ a, (Φ a).left = a.left ≫ (torsion.ι ((Over.pullback u).obj G) n).left ≫ pullback.fst G.hom u := by
    intro X t b hb
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hgp t b hb
    refine ⟨fun a => e ((TorsionUnram.torsionEquiv _ n _) a).1, ?_, ?_, ?_, ?_⟩
    · intro a₁ a₂ h12
      exact (TorsionUnram.torsionEquiv _ n _).injective (Subtype.ext (e.injective h12))
    · intro a
      rw [← map_pow, ((TorsionUnram.torsionEquiv _ n _) a).2, map_one]
    · intro w hw
      refine ⟨(TorsionUnram.torsionEquiv _ n _).symm ⟨e.symm w, by rw [← map_pow, hw, map_one]⟩, ?_⟩
      simp
    · intro a
      rw [he, ← Category.assoc]
      rfl
  obtain ⟨Φk, injk, -, surjk, hk⟩ := key (spMap h) (spMap h ≫ u) rfl
  obtain ⟨ΦU, -, powU, surjU, hUl⟩ := key (𝟙 (Sp U)) u (Category.id_comp u).symm
  obtain ⟨τ, rfl⟩ := surjk y hy
  have hb := sections_restrict_bijective U Ω k h (torsion ((Over.pullback u).obj G) n).hom
  obtain ⟨⟨s, hs⟩, hs'⟩ := hb.2 ⟨τ.left, Over.w τ⟩
  have hs'' : spMap h ≫ s = τ.left := congrArg Subtype.val hs'
  let σ : Over.mk (𝟙 (Sp U)) ⟶ torsion ((Over.pullback u).obj G) n := Over.homMk s hs
  refine ⟨ΦU σ, ⟨powU σ, ?_⟩, ?_⟩
  · rw [hk, hUl, ← hs'']
    simp [σ]
  · rintro P ⟨hP, hPy⟩
    obtain ⟨σ', rfl⟩ := surjU P hP
    have hσ' : σ'.left ≫ (torsion ((Over.pullback u).obj G) n).hom = 𝟙 _ := Over.w σ'
    let τ' : Over.mk (spMap h) ⟶ torsion ((Over.pullback u).obj G) n :=
      Over.homMk (spMap h ≫ σ'.left) (by rw [Category.assoc, hσ']; exact Category.comp_id _)
    have e0 : Φk τ' = Φk τ := by
      apply Over.OverMorphism.ext
      rw [hk, hPy, hUl]
      simp [τ']
    have e1 : spMap h ≫ σ'.left = τ.left := congrArg (fun q => q.left) (injk e0)
    have e2 := hb.1 (a₁ := ⟨σ'.left, hσ'⟩) (a₂ := ⟨s, hs⟩) (Subtype.ext (e1.trans hs''.symm))
    have e3 : σ' = σ := Over.OverMorphism.ext (congrArg Subtype.val e2)
    rw [e3]

end GlobalTheory.TorsionLiftVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosedStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ y : Over.mk (spMap h ≫ u) ⟶ G, y ^ n = 1 → ∃! P : Over.mk u ⟶ G, P ^ n = 1 ∧ y.left = spMap h ≫ P.left := by
  first | exact @GlobalTheory.TorsionLiftVal.torsion_lift_unique | exact GlobalTheory.TorsionLiftVal.torsion_lift_unique | (intros; apply GlobalTheory.TorsionLiftVal.torsion_lift_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRing

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ValReduction

theorem reduction_points : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u
  obtain ⟨e, he⟩ := GlobalTheory.ValPts.points_generic_mulEquiv U Ω S G hA.proper u
  let Vk : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  let φ : (Over.mk u ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G) :=
    MonoidHom.mk' (Vk ≫ ·) fun x y => MonObj.comp_mul Vk x y
  have hφ : ∀ P, (φ P).left = spMap h ≫ P.left := fun P => rfl
  have hes : ∀ (P : Over.mk u ⟶ G) y, y.left = spMap (algebraMap U Ω) ≫ P.left → e.symm y = P := by
    intro P y hy
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hy.trans (he P).symm)
  have hey : ∀ y, y.left = spMap (algebraMap U Ω) ≫ (e.symm y).left := fun y => by
    rw [← he]; simp
  refine ⟨φ.comp e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro P y y₀ hy hy₀
    apply Over.OverMorphism.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hes P y hy, hφ, hy₀]
  · intro f y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : e.symm (y ≫ f) = e.symm y ≫ f := hes _ _ (by
      rw [Over.comp_left, hey y, Category.assoc, Over.comp_left])
    rw [this]
    exact (Category.assoc Vk (e.symm y) f).symm
  · intro n hn
    refine ⟨fun y (hy : y ^ n = 1) => (show _ ^ n = 1 by rw [← map_pow, hy, map_one]), ?_, ?_⟩
    · intro y (hy : y ^ n = 1) y' (hy' : y' ^ n = 1) hyy
      have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
      have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
      obtain ⟨Q, -, hQ⟩ := GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed U Ω k h S G hA u n hn
        ((φ.comp e.symm.toMonoidHom) y) (by rw [← map_pow, hy, map_one])
      have h1 := hQ (e.symm y) ⟨hP, rfl⟩
      have h2 := hQ (e.symm y') ⟨hP', by rw [hyy]; rfl⟩
      exact e.symm.injective (h1.trans h2.symm)
    · intro y₀ (hy₀ : y₀ ^ n = 1)
      obtain ⟨P, ⟨hP, hPy⟩, -⟩ := GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed U Ω k h S G hA u n hn y₀ hy₀
      refine ⟨e P, (show e P ^ n = 1 by rw [← map_pow, hP, map_one]), ?_⟩
      apply Over.OverMorphism.ext
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hφ, hPy]
  · intro Lb hLb n hn y y' c hy hy' H
    have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
    have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    exact GlobalTheory.WeilSpecialise.weilIs_specialise U Ω S G hA Lb hLb u n hn (e.symm y) (e.symm y') c hP hP' y y'
      (hey y) (hey y') H k h _ _ rfl rfl

end GlobalTheory.ValReduction
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_reduction_points_abelianScheme_valuationRing : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  first | exact @GlobalTheory.ValReduction.reduction_points | exact GlobalTheory.ValReduction.reduction_points | (intros; apply GlobalTheory.ValReduction.reduction_points <;> assumption)
end
end
