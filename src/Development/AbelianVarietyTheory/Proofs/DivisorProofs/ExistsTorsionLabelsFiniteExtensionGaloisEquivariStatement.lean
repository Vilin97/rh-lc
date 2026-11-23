module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftFiniteCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExtEmb

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem exists_labels_finExt_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → ∃ (_ : Algebra (FractionRing R) (Kb R₁)) (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁), (∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) = algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) ∧ OneTrait D₁.toPre A₁ lab₁ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k) (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left := by
  intro R _ _ _ hR D A lab hT R₁ _ _ _ ρ hρ D₁ hD A₁ a ⟨ga, hga, gpa, la⟩
  obtain ⟨W₀, _, _, _, φ₀, G, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG, ⟨g₀, hg₀, gp₀, lb₀⟩, c₀, H₀⟩ := hT
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  obtain rfl := eq_fracMap hρ.2.1 hga
  obtain rfl := eq_fracMap i₀ hg₀
  letI : Algebra (FractionRing R) (Kb R₁) := ((algebraMap (FractionRing R₁) (Kb R₁)).comp (fracMap hρ.2.1)).toAlgebra
  have c' : Compat ρ (Kb R₁) := fun r => congrArg (algebraMap (FractionRing R₁) (Kb R₁)) (hga r)

  obtain ⟨W, _, _, _, io, φ, hW, iio, lio, lφ, hc⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ.2.1 hρ.2.2 W₀ hW₀ φ₀ l₀
  have iφ : Function.Injective φ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite R R₁ := hρ.2.2
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) ?_
    change Ideal.comap ρ (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker, hc, ← RingHom.injective_iff_ker_eq_bot]
    exact iio.comp i₀
  have := hW₀.1
  have := hW₀.2.2
  have := hW.1
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  have b₁ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D₂, h₁, A₂, U₂, b, hP, gpb, lb, hb⟩ := exists_pull_fib hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    b₀ b₁ io iio (map_maximalIdeal_le io) hG U₀
  obtain ⟨hc₀, T₀⟩ := exists_comp i₀ iio h₀ h₁
  obtain ⟨h', T'⟩ : ∃ h' : IsPullDeg φ D₁.toPre D₂.toPre, Tower hD h' hc₀ := by
    revert hc₀
    rw [← hc]
    exact fun hc₀ _ => exists_cancel hρ.2.1 iφ hD hc₀
  have fr : (fracMap iφ).comp (fracMap hρ.2.1) = (fracMap iio).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, fracMap_algebraMap]
      exact congrArg _ (RingHom.congr_fun hc r))
  obtain ⟨a₁, e₁, gp₁, lb₁⟩ := exists_fib_cancel (g' := spMap (fracMap iφ))
    ((Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap fr).trans (Geo.Tor.spMap_comp _ _))) gpa la gp₀ lb₀ gpb lb
  letI : Algebra (FractionRing R₁) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iφ)).toAlgebra
  letI : Algebra (FractionRing W₀) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iio)).toAlgebra
  letI : Algebra (FractionRing R) (Kb W) :=
    ((algebraMap (FractionRing W) (Kb W)).comp ((fracMap iφ).comp (fracMap hρ.2.1))).toAlgebra
  have cφ : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iφ r)
  have cio : Compat io (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iio r)
  have cρ : Compat ρ (Kb W) := fun r =>
    congrArg (fun t => algebraMap (FractionRing W) (Kb W) (fracMap iφ t)) (fracMap_algebraMap hρ.2.1 r)
  have cc : Compat (io.comp φ₀) (Kb W) := fun r => (cρ r).trans ((cφ _).trans
    (congrArg (fun t => algebraMap (FractionRing W) (Kb W) (algebraMap W _ t)) (RingHom.congr_fun hc r)))
  have cφ₀ : Compat φ₀ (Kb W) := fun r => (cc r).trans (cio _).symm
  obtain ⟨em⟩ := nonempty_lift (FractionRing R₁) (Kb W)
  obtain ⟨j⟩ := nonempty_lift (FractionRing W₀) (Kb W)
  let emR : Kb R₁ →ₐ[FractionRing R] Kb W := ⟨em.toRingHom, fun t => em.commutes (fracMap hρ.2.1 t)⟩
  have a₀K : algebraMap (FractionRing R) (Kb W₀) = (algebraMap (FractionRing W₀) (Kb W₀)).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (fracMap_algebraMap i₀ r).symm))
  let jR : Kb W₀ →ₐ[FractionRing R] Kb W := ⟨j.toRingHom, fun t => by
    rw [a₀K]
    exact (j.commutes (fracMap i₀ t)).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (RingHom.congr_fun fr t).symm)⟩

  obtain ⟨em'⟩ := nonempty_lift (FractionRing R) (Kb R₁)
  letI : Algebra (Kb R) (Kb W) := (emR.comp em').toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) (Kb W) :=
    IsScalarTower.of_algebraMap_eq fun x => ((emR.comp em').commutes x).symm
  let emK : Kb R →ₐ[FractionRing R] Kb R₁ := em'.comp ((jR.comp em₀).restrictNormal (Kb R))
  have hK : (emR.comp emK).toRingHom = (jR.comp em₀).toRingHom :=
    RingHom.ext fun x => (jR.comp em₀).restrictNormal_commutes (Kb R) x

  have ex : ∀ (k : ℕ) (p' : QkPt D₁.toPre (Kb R₁) k), ∃ x : TFK (R := R₁) (Kb R₁) ⟶ A₁.A, 1 ≤ k →
      ∃ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k), QkExt emK.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
        IsPullGtF ρ hD (Kb R₁) p₁.g p'.g ∧ x.left ≫ a = spMap emK.toRingHom ≫ (lab k p).left := by
    intro k p'
    by_cases hk : 1 ≤ k
    · obtain ⟨p₁, hy, hg⟩ := qkPullExists hGF R R₁ ρ D.toPre D₁.toPre hD (Kb R₁) c' k p'
      obtain ⟨p, hp⟩ := exists_of_ext hB emK hk p₁
      obtain ⟨x, hx⟩ := exists_lift_pt gpa.1 emK.toRingHom emK.comp_algebraMap (lab k p)
      exact ⟨x, fun _ => ⟨p, p₁, hp, hy, hg, hx⟩⟩
    · exact ⟨η[A₁.A] |> fun e => toUnit _ ≫ e, fun h => absurd h hk⟩
  choose lab₁ hlab₁ using ex
  refine ⟨inferInstance, emK, lab₁, c', ?_, ?_⟩
  ·
    refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf io)).obj G, inferInstance, inferInstance, D₂, A₂,
      U₂, h', a₁, inferInstance, em, hW, iφ, lφ, IsSemiAbelian.pullback _ G hG,
      ⟨fracMap iφ, fracMap_algebraMap iφ, gp₁, lb₁⟩, cφ, ?_⟩
    intro k hk p' p₁' p'' x₁ y₁ y₂ y₃ y₄
    obtain ⟨p, p₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain ⟨r, hr⟩ := exists_ext hB emR p₁
    have r₁ : IsPullGtF ρ hD (Kb W) r.g p₁'.g := isPullGtF_ext hD cρ em.toRingHom em.comp_algebraMap z₃ hr y₁
    have r₂ := T'.isPullGtF cc r₁ y₃
    have hq : QkExt (jR.comp em₀).toRingHom p r := by
      rw [← hK]
      exact qkExt_trans z₁ hr
    have key : spMap (emR.comp emK).toRingHom ≫ (lab k p).left = spMap (jR.comp em₀).toRingHom ≫ (lab k p).left := by
      rw [hK]
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ p
    obtain ⟨r', hr'⟩ := exists_ext hB jR q₁
    obtain rfl : r = r' := ext_unique hB (jR.comp em₀) hq (qkExt_trans hq₁ hr')
    let q₀ := pullQk h₀ hGF c₀ hB D₀.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp₀.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab k p)
    have t₀ := H₀ k hk p q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt h₀ hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W₀ _ b₀ D₀ A₀ G hG U₀ _ (Kb W) j k hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    have t₁ := (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀
    have s₁ : IsPullGtF φ₀ h₀ (Kb W) r.g q₀'.g :=
      isPullGtF_ext h₀ cφ₀ j.toRingHom j.comp_algebraMap (isPullGtF_pullGt h₀ hGF c₀ _) hr' hq₀'
    have s₂ := isPullGtF_pullGt h₁ hGF cio q₀'.g
    rw [← pullGt_unique hc₀ cc r₂ (T₀.isPullGtF cc s₁ s₂)] at s₂
    have ey : p''.y = h₁.xe.symm q₀'.y := by
      apply hc₀.xe.injective
      have u₁ : hc₀.xe p''.y = r.y := by
        rw [← T'.xe_eq, y₂, AddEquiv.apply_symm_apply, y₁.1, z₂, AddEquiv.apply_symm_apply, hr.1]
      rw [u₁, ← T₀.xe_eq, AddEquiv.apply_symm_apply, hq₀'.1, hr'.1]
      exact (h₀.xe.apply_symm_apply _).symm
    have ex₁ : x₁.left ≫ b = x₀'.left := by
      apply gp₀.1.hom_ext
      · rw [Category.assoc, ← e₁, ← Category.assoc, y₄, Category.assoc, z₄, hx₀', Category.assoc, hx₀, ← Category.assoc,
          ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp]
        exact key
      · rw [Category.assoc, gpb.1.w, ← Category.assoc, Over.w x₁, Over.w x₀']
        exact (Geo.Tor.spMap_comp _ _).symm
    refine h5.qkBaseChange W₀ W _ _ b₀ b₁ io D₀ A₀ G U₀ _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A₂ D₂ h₁
      U₂ hP (Kb W) cio k hk q₀' x₀' p'' x₁ ey s₂ ?_ t₁
    rw [hb, ← Category.assoc, ex₁]
  ·
    intro k hk p p₁ p' e₁' e₂' e₃'
    obtain ⟨q, q₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain rfl : q₁ = p₁ := qk_ext (hD.xe.symm.injective (by rw [← z₂]; exact e₂')) (pullGt_unique' hD z₃ e₃')
    obtain rfl := qkExt_inj hB emK z₁ e₁'
    exact z₄

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicKb

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabBC

open GlobalTheory GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem qkExt_id' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

theorem isAlgebraic_kb {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁)
    (hρ : ρ.Finite) [Algebra (FractionRing R) (Kb R₁)]
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) :
    Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := by
  letI : Algebra R R₁ := ρ.toAlgebra
  have h1 : ∀ r : R, algebraMap R (Kb R₁) r = algebraMap R₁ (Kb R₁) (ρ r) := fun r => by
    rw [IsScalarTower.algebraMap_apply R (FractionRing R₁) (Kb R₁), IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁),
      IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
    rfl
  haveI : IsScalarTower R R₁ (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => h1 r
  haveI : IsScalarTower R (FractionRing R) (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [h1, hc, IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
  haveI : Module.Finite R R₁ := hρ
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsAlgebraic.of_finite R R₁
  haveI : Algebra.IsAlgebraic R₁ (Kb R₁) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R₁) (K := FractionRing R₁)).2 inferInstance
  haveI : Algebra.IsAlgebraic R (Kb R₁) := Algebra.IsAlgebraic.trans R R₁ (Kb R₁)
  exact (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := FractionRing R)).1 inferInstance

theorem galEqN_of_rel {R R₁ : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁]
    [IsLocalRing R₁] (ρ : R →+* R₁) (hρ : FinExt ρ) (D : DegData R (maximalIdeal R))
    (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A : PolAV (Sp (FractionRing R)))
    (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (hfib : IsFib ρ A A₁ a) (lab : Labels D.toPre A)
    (n : ℕ) (hn : 1 ≤ n) (hGal : GalEqN n lab) [Algebra (FractionRing R) (Kb R₁)]
    (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁)
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r)))
    (hrel : ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k)
      (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y →
      IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left) :
    GalEqN n lab₁ := by
  obtain ⟨ga, hga, hpb, -⟩ := hfib
  have hK : algebraMap (FractionRing R) (Kb R₁) = (algebraMap (FractionRing R₁) (Kb R₁)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, hga, hc])
  haveI : Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := isAlgebraic_kb ρ hρ.2.2 hc
  let mu : Kb R₁ →ₐ[FractionRing R] Kb R := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hsurj : Function.Surjective em := fun z => by
    obtain ⟨w, hw⟩ := (Algebra.IsAlgebraic.algHom_bijective (em.comp mu)).2 z
    exact ⟨mu w, hw⟩
  let τ : Kb R ≃ₐ[FractionRing R] Kb R₁ := AlgEquiv.ofBijective em ⟨em.toRingHom.injective, hsurj⟩
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  have hG := hL.globalFns
  have hB := D.tau_bimult
  have hB₁ := D₁.tau_bimult
  have hF : Compat ρ (Kb R₁) := hc
  intro σ₁ j P P' hPP'
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn
  set e : Kb R →+* Kb R₁ := em.toRingHom with he_def
  set e' : Kb R₁ →+* Kb R := τ.symm.toAlgHom.toRingHom with he'_def
  set s₁ : Kb R₁ →+* Kb R₁ := σ₁.toRingHom with hs₁_def
  have hee' : e.comp e' = RingHom.id _ := RingHom.ext fun x => τ.apply_symm_apply x
  have hfσ : s₁.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) := by
    rw [hK, ← RingHom.comp_assoc]
    exact congrArg (fun f => f.comp ga) σ₁.comp_algebraMap
  have hfσ₁ : s₁.comp (algebraMap (FractionRing R₁) (Kb R₁)) = algebraMap (FractionRing R₁) (Kb R₁) :=
    σ₁.comp_algebraMap
  have hfe : e.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R₁) := em.comp_algebraMap
  have hfe' : e'.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R) :=
    τ.symm.toAlgHom.comp_algebraMap
  have hfid : (RingHom.id (Kb R₁)).comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) :=
    RingHom.id_comp _

  let σ : Kb R →ₐ[FractionRing R] Kb R :=
    τ.symm.toAlgHom.comp ((({ σ₁.toRingHom with commutes' := fun x => RingHom.congr_fun hfσ x } : Kb R₁ →ₐ[FractionRing R] Kb R₁)).comp em)
  have hσ_def : σ.toRingHom = e'.comp (s₁.comp e) := rfl
  have hfσR : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hes : e.comp σ.toRingHom = s₁.comp e := by
    rw [hσ_def, ← RingHom.comp_assoc, hee', RingHom.id_comp]
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P
  obtain ⟨q', rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P'
  have hq' : q' = qkExt hB s₁ hfσ q := by
    apply GlobalTheory.QkPullEquiv.pullQk_injective hD hG hF hB hB₁
    rw [(qkExt_iff hB₁ s₁ hfσ₁ _ _).1 hPP',
      (qkExt_iff hB₁ s₁ hfσ₁ _ _).1 (GlobalTheory.QkRationalExt.qkExt_pullQk hD hG hB hB₁ hF hF s₁ hfσ hfσ₁ q)]
  have hid : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), qkExt hB (RingHom.id _) hfid z = z := fun z =>
    ((qkExt_iff hB _ hfid z z).1 (qkExt_id' z)).symm

  have hpq : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), QkExt e (qkExt hB e' hfe' z) z := fun z => by
    rw [qkExt_iff hB e hfe, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' e hfe (RingHom.id _) hfid hee', hid]
  have hσpp : QkExt σ.toRingHom (qkExt hB e' hfe' q) (qkExt hB e' hfe' q') := by
    rw [qkExt_iff hB _ hfσR, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' σ.toRingHom hfσR (e'.comp s₁)
      (by rw [RingHom.comp_assoc, hfσ, hfe']) (by rw [hσ_def, RingHom.comp_assoc, RingHom.comp_assoc, hee',
        RingHom.comp_id]), hq', GlobalTheory.QkRationalExt.qkExt_qkExt hB s₁ hfσ e' hfe' (e'.comp s₁) _ rfl]
  have hgal := hGal σ j _ _ hσpp
  have h₁ := hrel _ hk _ _ _ (hpq q) ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).2
  have h₂ := hrel _ hk _ _ _ (hpq q') ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).2
  apply hpb.1.hom_ext
  · rw [h₂, Category.assoc, h₁, hgal, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hes]
  · rw [Category.assoc, Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q')), Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q))]
    show jFK (R := R₁) (Kb R₁) = spMap s₁ ≫ jFK (R := R₁) (Kb R₁)
    rw [spMap_comp', hfσ₁]

end GlobalTheory.Mum.LabBC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsFiniteExtensionGaloisEquivari

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_labels_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (n : ℕ), OneTrait D.toPre A lab → GalEqN n lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → 1 ≤ n → ∃ lab₁ : Labels D₁.toPre A₁, OneTrait D₁.toPre A₁ lab₁ ∧ GalEqN n lab₁ := by
  intro R _ _ _ hB D A lab n hOne hGal R₁ _ _ _ ρ hρ D₁ hD A₁ a hfib hn
  obtain ⟨hD⟩ := hD
  obtain ⟨_, em, lab₁, hc, hOne₁, hrel⟩ :=
    exists_labels_finExt_emb R hB D A lab hOne R₁ ρ hρ D₁ hD A₁ a hfib
  exact ⟨lab₁, hOne₁, LabBC.galEqN_of_rel ρ hρ D D₁ hD A A₁ a hfib lab n hn hGal em lab₁ hc hrel⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsFiniteExtensionGaloisEquivariStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_torsionLabels_finiteExtension_galoisEquivariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (n : ℕ), OneTrait D.toPre A lab → GalEqN n lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → 1 ≤ n → ∃ lab₁ : Labels D₁.toPre A₁, OneTrait D₁.toPre A₁ lab₁ ∧ GalEqN n lab₁ := by
  first | exact @GlobalTheory.Mum.exists_labels_finExt_galEqN | exact GlobalTheory.Mum.exists_labels_finExt_galEqN | (intros; apply GlobalTheory.Mum.exists_labels_finExt_galEqN <;> assumption)
end
end
