module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaEqOfMkEq
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlatStatement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFormallyUnramifiedOfEqAtClosedPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem eq_of_unramified_of_closedPoint : ∀ {S T : Scheme.{0}} (f : T ⟶ S) [FormallyUnramified f]
    [LocallyOfFiniteType f] (R : CommRingCat.{0}) [IsLocalRing R] (u₁ u₂ : Spec R ⟶ T) (h : u₁ ≫ f = u₂ ≫ f)
    (K : Type) [Field K] (k : Sp K ⟶ Spec R) (hk : ∀ x, k x = IsLocalRing.closedPoint R)
    (hku : k ≫ u₁ = k ≫ u₂), u₁ = u₂ := by
  intro S T f _ _ R _ u₁ u₂ h K _ k hk hku
  let g : Spec R ⟶ pullback f f := pullback.lift u₁ u₂ h
  have hkg : k ≫ g = (k ≫ u₁) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp [g, pullback.lift_fst]
    · simp [g, hku, pullback.lift_snd]
  obtain ⟨x⟩ : Nonempty (Sp K) := (inferInstance : Nonempty (PrimeSpectrum K))
  have hc : g (IsLocalRing.closedPoint R) ∈ Set.range (pullback.diagonal f) := by
    refine ⟨(k ≫ u₁) x, ?_⟩
    rw [← hk x, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hkg]
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hr : Set.range g ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint y
    exact (hs.map g.continuous).mem_open hopen hc
  have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) g hr
  have h1 : u₁ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.fst f f
        = g ≫ pullback.fst f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at e
    exact e.symm
  have h2 : u₂ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.snd f f
        = g ≫ pullback.snd f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at e
    exact e.symm
  exact h1.trans h2.symm

end GlobalTheory.TorsSpec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFormallyUnramifiedOfEqAtClosedPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi


theorem _root_.GlobalTheory.T.eq_of_formallyUnramified_of_eq_at_closedPoint : ∀ {S T : Scheme.{0}} (f : T ⟶ S) [FormallyUnramified f]
    [LocallyOfFiniteType f] (R : CommRingCat.{0}) [IsLocalRing R] (u₁ u₂ : Spec R ⟶ T) (h : u₁ ≫ f = u₂ ≫ f)
    (K : Type) [Field K] (k : Sp K ⟶ Spec R) (hk : ∀ x, k x = IsLocalRing.closedPoint R)
    (hku : k ≫ u₁ = k ≫ u₂), u₁ = u₂ := by
  first | exact @GlobalTheory.TorsSpec.eq_of_unramified_of_closedPoint | exact GlobalTheory.TorsSpec.eq_of_unramified_of_closedPoint | (intros; apply GlobalTheory.TorsSpec.eq_of_unramified_of_closedPoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassTorsionPointLocalScheme

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_section_of_isDominant {D G X' V Y₀ Y : Scheme.{0}} [IsReduced D] (g : G ⟶ X') [IsSeparated g]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (σ : D ⟶ G) (s : V ⟶ G) (hs : s ≫ g = ℓ) (y₀ : Y₀ ⟶ D) [IsDominant y₀]
    (z₀ : Y₀ ⟶ V) (h₀ : y₀ ≫ σ = z₀ ≫ s) (y : Y ⟶ D) (z : Y ⟶ V) (h : y ≫ σ ≫ g = z ≫ ℓ) :
    y ≫ σ = z ≫ s := by
  have h₀' : y₀ ≫ σ ≫ g = z₀ ≫ ℓ := by rw [reassoc_of% h₀, hs]
  have : IsReduced (pullback (σ ≫ g) ℓ) := isReduced_of_isOpenImmersion (pullback.fst (σ ≫ g) ℓ)
  have hd : IsDominant (pullback.lift y₀ z₀ h₀') := by
    constructor
    have h1 : Dense (Set.range y₀) := y₀.denseRange
    have h2 := h1.preimage (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.isOpenMap
    refine h2.mono ?_
    rintro u ⟨t, ht⟩
    refine ⟨t, (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.injective ?_⟩
    rw [← ht, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have key : pullback.fst (σ ≫ g) ℓ ≫ σ = pullback.snd (σ ≫ g) ℓ ≫ s := by
    refine ext_of_isDominant_of_isSeparated (s := g) ?_ (pullback.lift y₀ z₀ h₀') ?_
    · rw [Category.assoc, Category.assoc, hs, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₀]
  have := pullback.lift y z h ≫= key
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this

theorem fromSpecStalk_killed {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) [Etale (torsion G n).hom]
    (a : G ⟶ G) [IsMonHom a] (ha : a ≫ mulN G n = mulN G n ≫ a)
    (K : Type) [Field K] (P : Sp K ⟶ (torsion G n).left)
    (hP : P ≫ (torsion.ι G n).left ≫ a.left =
      P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K) :
    (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left ≫ a.left =
      (torsion G n).left.fromSpecStalk (P x) ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
  have h0 : (MonObj.one : 𝟙_ (Over X') ⟶ G) ≫ mulN G n = (MonObj.one : 𝟙_ (Over X') ⟶ G) := by
    have e : (MonObj.one : 𝟙_ (Over X') ⟶ G) = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, e, one_pow]
  obtain ⟨u₁, hu₁⟩ := exists_lift_torsion n (torsion.ι G n ≫ a)
    (by rw [Category.assoc, ha, ← Category.assoc, hι, MonObj.one_comp])
  obtain ⟨u₂, hu₂⟩ := exists_lift_torsion n (1 : torsion G n ⟶ G)
    (by rw [Hom.one_def, Category.assoc, h0])
  have e₁ : u₁.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ a.left := congrArg (·.left) hu₁
  have e₂ : u₂.left ≫ (torsion.ι G n).left = (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have := congrArg (·.left) hu₂
    simp only [Hom.one_def, Over.comp_left] at this
    rw [this]
    congr 1
  have := mono_torsion_ι G n
  have key : (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₁.left =
      (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₂.left := by
    refine GlobalTheory.T.eq_of_formallyUnramified_of_eq_at_closedPoint (torsion G n).hom _ _ _ ?_ K (Spec.map (Scheme.stalkClosedPointTo P)) ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, Over.w]
    · intro x
      obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact IsLocalRing.comap_closedPoint (Scheme.stalkClosedPointTo P).hom
    · rw [← Category.assoc, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
        ← cancel_mono (torsion.ι G n).left, Category.assoc, Category.assoc, e₁, e₂, hP]
  rw [← e₁, ← e₂, reassoc_of% key]

theorem exists_valAt : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom] (act : OAct (𝓞 E) G) (I : Ideal (𝓞 E))
    (hex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (P : Sp Ω ⟶ G.left), P ≫ G.hom = x ≫ ℓ →
      (∀ a ∈ I, P ≫ (act.act a).left = P ≫ G.hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) → ∃ c, P = x ≫ w c)
    (K : Type) [Field K] [IsAlgClosed K] (P : Sp K ⟶ (torsion G n).left)
    (hP : ∀ a ∈ I, P ≫ (torsion.ι G n).left ≫ (act.act a).left = P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K), ∃ c, GlobalTheory.TorsSpec.ValAt G n ℓ w (P x) c := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ act I hex K _ _ P hP x
  have := GlobalTheory.GrpTangent.etale_torsion G hn
  have := isDomain_stalk_of_etale (torsion G n).hom (P x)
  obtain ⟨Ω, _, _, y₀, hy₀, _⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((torsion G n).left.presheaf.stalk (P x))
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat (torsion G n).hom (P x) ℓ Ω y₀ hy₀
  have hw' : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  obtain ⟨c, hc⟩ := hex Ω z₀ (y₀ ≫ (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left)
    (by rw [Category.assoc, Category.assoc, hw', hz₀]) (fun a ha => by
      have := act.hom a
      have h := fromSpecStalk_killed G n (act.act a)
        (by rw [← act_natCast act, ← act.mul, ← act.mul, mul_comm]) K P (hP a ha) x
      simp only [Category.assoc]
      rw [h, reassoc_of% hw'])
  refine ⟨c, fun Ω' _ _ y z h => ?_⟩
  exact eq_section_of_isDominant G.hom ℓ _ (w c) (hw c) y₀ z₀ hc y z (by rw [Category.assoc, hw', h])

end GlobalTheory.TorsSpec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassTorsionPointLocalSchemeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi


theorem _root_.GlobalTheory.T.exists_class_torsionPoint_localScheme : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom] (act : OAct (𝓞 E) G) (I : Ideal (𝓞 E))
    (hex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (P : Sp Ω ⟶ G.left), P ≫ G.hom = x ≫ ℓ →
      (∀ a ∈ I, P ≫ (act.act a).left = P ≫ G.hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) → ∃ c, P = x ≫ w c)
    (K : Type) [Field K] [IsAlgClosed K] (P : Sp K ⟶ (torsion G n).left)
    (hP : ∀ a ∈ I, P ≫ (torsion.ι G n).left ≫ (act.act a).left = P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K), ∃ c, GlobalTheory.TorsSpec.ValAt G n ℓ w (P x) c := by
  first | exact @GlobalTheory.TorsSpec.exists_valAt | exact GlobalTheory.TorsSpec.exists_valAt | (intros; apply GlobalTheory.TorsSpec.exists_valAt <;> assumption)
end
end
