module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLocalPeriodMatrix
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenPosDefOfContinuous
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundleStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SameCompOfIsHolTo
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyComplexPointEqOfSamePeriodMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNhdsSubsetImage

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelOpen

theorem image_mem_nhds_of_injOn {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {a : Fin n → ℂ}
    (ha : a ∈ U) : f '' U ∈ nhds (f a) := by
  have han : AnalyticAt ℂ f a := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n U (fun x => f x i) hU (differentiableOn_pi.mp hf i) a ha
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn n U f hU hf hinj a ha
  have hm : Filter.map f (nhds a) = nhds (f a) :=
    han.hasStrictFDerivAt.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hb.2)
  rw [← hm]
  exact Filter.image_mem_map (hU.mem_nhds ha)

theorem eq_of_out {J R : Type} {s t : Matrix J J R} (hs : s.IsSymm) (ht : t.IsSymm)
    (h : ∀ z : Sym2 J, s z.out.1 z.out.2 = t z.out.1 z.out.2) : s = t := by
  ext i j
  have h1 := h s(i, j)
  have h2 : s((s(i, j) : Sym2 J).out.1, (s(i, j) : Sym2 J).out.2) = s(i, j) :=
    Quot.out_eq (s(i, j) : Sym2 J)
  rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rwa [h3, h4] at h1
  · rw [h3, h4] at h1
    rw [← hs.apply i j, ← ht.apply i j]
    exact h1

theorem exists_nhds_subset_image :
    ∀ (h : ℕ) (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ) (b₀ : Fin (h * (h + 1) / 2) → ℂ), IsOpen B → b₀ ∈ B → (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → Set.InjOn τ B → ∃ N ∈ nhds (τ b₀), ∀ t ∈ N, t.IsSymm → (t.map Complex.im).PosDef → ∃ b ∈ B, τ b = t := by
  intro h B τ b₀ hB hb₀ hd hs hinj
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (GlobalTheory.card_sym2_fin h)
  let p : Matrix (Fin h) (Fin h) ℂ → (Fin (h * (h + 1) / 2) → ℂ) :=
    fun t k => t (e.symm k).out.1 (e.symm k).out.2
  have hpc : Continuous p := continuous_pi fun k => continuous_id.matrix_elem _ _
  have hp : ∀ s t : Matrix (Fin h) (Fin h) ℂ, s.IsSymm → t.IsSymm → p s = p t → s = t := by
    intro s t hs' ht' hst
    refine eq_of_out hs' ht' fun z => ?_
    have := congrFun hst (e z)
    simpa only [p, Equiv.symm_apply_apply] using this
  have key := image_mem_nhds_of_injOn (f := fun b => p (τ b)) hB
    (differentiableOn_pi.mpr fun k => hd _ _)
    (fun x hx y hy hxy => hinj hx hy (hp _ _ (hs x hx).1 (hs y hy).1 hxy)) hb₀
  refine ⟨_, hpc.continuousAt.preimage_mem_nhds key, ?_⟩
  rintro t ⟨b, hb, hbt⟩ ht -
  exact ⟨b, hb, hp _ _ (hs b hb).1 ht hbt⟩

end GlobalTheory.SiegelOpen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSeparatingPairs

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.EtaleLocInj

theorem exists_separating_pairs {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (h : φ.Etale) :
    ∃ s : Finset (S × S), ∑ p ∈ s, p.1 * p.2 = 1 ∧ ∀ e e' : S →+* ℂ, e.comp φ = e'.comp φ →
      ∑ p ∈ s, e p.1 * e' p.2 ≠ 0 → e = e' := by
  algebraize [φ]
  obtain ⟨t, ht, h1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := S)).1 inferInstance
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  refine ⟨s, ?_, fun e e' hee hne => ?_⟩

  · simpa [map_sum] using h1
  · letI : Algebra R ℂ := (e.comp φ).toAlgebra
    let a : S →ₐ[R] ℂ := { e with commutes' := fun _ => rfl }
    let a' : S →ₐ[R] ℂ := { e' with commutes' := fun r => (RingHom.congr_fun hee r).symm }
    let F := Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
    ext x
    have h2 := congrArg F (ht x)

    simp only [F, map_mul, map_sub, map_sum, Algebra.TensorProduct.lift_tmul, map_one, map_zero] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · have h4 := (sub_eq_zero.1 h3).symm
      rw [_root_.one_mul, _root_.mul_one] at h4
      exact h4
    · exact (hne h3).elim

theorem eq_of_valAtHom_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x x' : Sp ℂ ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valAtHom x U h = valAtHom x' U h') : x = x' := by
  rw [← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h,
    ← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h']
  congr 2
  ext1
  exact e

theorem exists_open_injOn :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ), Etale π → IsOpen B → b₀ ∈ B → IsHolTo B y → ∃ B' : Set (Fin m → ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ ∀ b ∈ B', ∀ b' ∈ B', y b ≫ π = y b' ≫ π → y b = y b' := by
  intro X Y π m B y b₀ hπ _ hb₀ hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π (y b₀ (default : PrimeSpectrum ℂ)))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show y b₀ (default : PrimeSpectrum ℂ) ∈ ((π ⁻¹ᵁ V : X.Opens) : Set X) from hxV) (π ⁻¹ᵁ V).isOpen
  have e : U ≤ π ⁻¹ᵁ V := hUV
  obtain ⟨s, hs1, hs⟩ := exists_separating_pairs _ (π.etale_appLE hV hU e)
  set C : Set (Fin m → ℂ) := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} with hC
  have hCo : IsOpen C := (hy U 0).1
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hb₀C : b₀ ∈ C := ⟨hb₀, h₀⟩
  have hc : ∀ f : Γ(X, U), ContinuousAt (fun b => valAt' (y b) U f) b₀ := fun f =>
    (hy U f).2.continuousOn.continuousAt (hCo.mem_nhds hb₀C)
  let F : (Fin m → ℂ) × (Fin m → ℂ) → ℂ := fun q => ∑ p ∈ s, valAt' (y q.1) U p.1 * valAt' (y q.2) U p.2
  have hF : ContinuousAt F (b₀, b₀) := by
    refine tendsto_finsetSum _ fun p _ => ?_
    exact ((hc p.1).comp_of_eq continuousAt_fst rfl).mul ((hc p.2).comp_of_eq continuousAt_snd rfl)
  have hF0 : F (b₀, b₀) ≠ 0 := by
    simp only [F, ← valAt'_mul, ← valAt'_sum, hs1, valAt'_one _ h₀]
    exact one_ne_zero
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hF.eventually_ne hF0)
  obtain ⟨B', hB'sub, hB'o, hB'⟩ := mem_nhds_iff.1
    (Filter.inter_mem (hCo.mem_nhds hb₀C) (Filter.inter_mem hu hv))
  refine ⟨B', hB'o, hB', fun b hb => (hB'sub hb).1.1, fun b hb b' hb' hbb => ?_⟩
  have h1 := (hB'sub hb).1.2
  have h2 := (hB'sub hb').1.2
  refine eq_of_valAtHom_eq hU _ _ h1 h2 (hs _ _ ?_ ?_)
  · ext f
    rw [RingHom.comp_apply, RingHom.comp_apply, ← valAt'_eq_valAtHom, ← valAt'_eq_valAtHom,
      valAt'_appLE _ _ _ _ _ _ h1, valAt'_appLE _ _ _ _ _ _ h2, hbb]
  · simp only [← valAt'_eq_valAtHom]
    have h3 : F (b, b') ≠ 0 := huv (Set.mk_mem_prod (hB'sub hb).2.1 (hB'sub hb').2.2)
    exact h3

end GlobalTheory.EtaleLocInj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelNearby
open GlobalTheory.ZM.SiegPull GlobalTheory.RigidTranslate

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

theorem exists_polPB (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), PolPB P' P f φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB _ _ f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem transl_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (t : 𝟙_ (Over S) ⟶ G) (t' : 𝟙_ (Over S') ⟶ G')
    (e : t'.left ≫ φ = f ≫ t.left) :
    ((toUnit G' ≫ t') * 𝟙 G').left ≫ φ = φ ≫ ((toUnit G ≫ t) * 𝟙 G).left := by
  have h₁ := h.2 G' (toUnit G' ≫ t') (𝟙 G') (toUnit _ ≫ t) (pushPt h.1.w (𝟙 G')) (by
    rw [Over.comp_left, Over.comp_left, toUnit_left, toUnit_left, Category.assoc, e]
    exact Category.assoc _ _ _) rfl
  have h₂ : pushPt h.1.w (𝟙 G') ≫ ((toUnit G ≫ t) * 𝟙 G) = (toUnit _ ≫ t) * pushPt h.1.w (𝟙 G') := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  rw [← h₁, ← h₂, Over.comp_left]
  exact congrArg (· ≫ _) (Category.id_comp φ)

theorem exists_section_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (t : 𝟙_ (Over S) ⟶ G) (n : ℕ) (ht : t ^ n = 1) :
    ∃ t' : 𝟙_ (Over S') ⟶ G', t' ^ n = 1 ∧ t'.left ≫ φ = f ≫ t.left := by
  have w : (f ≫ t.left) ≫ G.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w t]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  let t' : 𝟙_ (Over S') ⟶ G' := Over.homMk (h.1.lift (f ≫ t.left) (𝟙 S') w) (h.1.lift_snd _ _ _)
  have e : t'.left ≫ φ = f ≫ t.left := h.1.lift_fst _ _ _
  have e₁ : pushHom h _ t' = toUnit _ ≫ t := Over.OverMorphism.ext (by
    rw [Over.comp_left, toUnit_left]
    exact e.trans (congrArg (· ≫ t.left) (Category.id_comp f).symm))
  have e₂ : pushHom h _ (t' ^ n) = pushHom h _ 1 := by
    rw [map_pow, e₁, map_one, ← MonObj.comp_pow, ht, MonObj.comp_one]
  refine ⟨t', Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e₂) ?_), e⟩
  exact (Over.w _).trans (Over.w _).symm

variable {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}

theorem exists_sqOf_polPB (hL : Out.Laws) {R : Type} [CommRing R] {c : SiegPre h k ζ s} {f : Sp R ⟶ S}
    {Q : Out.PolAV (Sp R)} {φ : Q.A.left ⟶ c.A.left} (hQ : SqOf Q c f φ) (hT : TorsConst Q.A 2) (p : Sp ℂ ⟶ Sp R)
    {P₀ : Out.PolAV (Sp ℂ)} {φ₀ : P₀.A.left ⟶ c.A.left} (hP : SqOf P₀ c (p ≫ f) φ₀) :
    ∃ (Q' : Out.PolAV (Sp R)) (φ' : Q'.A.left ⟶ c.A.left) (ψ : P₀.A.left ⟶ Q'.A.left),
      SqOf Q' c f φ' ∧ PolPB P₀ Q' p ψ ∧ ψ ≫ φ' = φ₀ := by
  obtain ⟨Q₀, ψ₀, hpb⟩ := exists_polPB hL.polBaseChange Q p
  have h₀ := (sqOf_calculus h k o ζ S _ _ s c f).1 p Q Q₀ φ ψ₀ hQ hpb
  obtain ⟨e, he, heφ, hlam⟩ := (sqOf_calculus h k o ζ S _ S s c (p ≫ f)).2.1 Q₀ P₀ _ _ h₀ hP
  obtain ⟨t₀, ht₀, i₀⟩ := GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle hL ℂ Q₀ P₀ e he hlam
  obtain ⟨t, ht, hy⟩ := hT ℂ ((𝟙_ (Over (Sp ℂ))).hom ≫ p) (pushHom hpb.1 _ t₀) (by rw [← map_pow, ht₀, map_one])
  have et : t₀.left ≫ ψ₀ = p ≫ t.left := by
    refine (congrArg (fun q => q.left) hy).trans ?_
    rw [Over.comp_left, toUnit_left]
    exact congrArg (· ≫ t.left) (Category.id_comp p)
  obtain ⟨Q', e', he', hg', hlam', i'⟩ := exists_rigid_translate hL R Q t ht
  have ee : e'.inv.left ≫ e'.hom.left = 𝟙 _ := by rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]
  have : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have gp : IsGrpPullback P₀.A Q'.A p (e.hom.left ≫ ψ₀ ≫ e'.inv.left) :=
    ((isGrpPullback_of_iso e).comp (hpb.1.comp (isGrpPullback_of_iso e'.symm))).congr
      ((Category.id_comp _).trans (Category.comp_id _)) rfl
  have hQ' := (sqOf_calculus h k o ζ S _ S s c f).2.2 Q Q' φ e' he' hg' hlam' hQ
  refine ⟨Q', e'.hom.left ≫ φ, e.hom.left ≫ ψ₀ ≫ e'.inv.left, hQ', ⟨gp, hP.2.1.trans hQ'.2.1.symm, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart Q.isLB ((p ≫ t.left) (default : PrimeSpectrum ℂ))
    have j₁ := lbIso_diff_pull Q.isLB (e'.hom ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A)).left (toUnit Q'.A ≫ t).left
      (e.hom.left ≫ ψ₀ ≫ e'.inv.left) i fun z => by
        have : (e.hom.left ≫ ψ₀ ≫ e'.inv.left) ≫ (toUnit Q'.A ≫ t).left = P₀.A.hom ≫ p ≫ t.left := by
          rw [Over.comp_left, toUnit_left, ← Category.assoc, gp.1.w, Category.assoc]
        rw [this, Scheme.Hom.comp_apply, Subsingleton.elim (α := PrimeSpectrum ℂ) (P₀.A.hom z) default]
        exact hi
    have E : (e.hom.left ≫ ψ₀ ≫ e'.inv.left) ≫ (e'.hom ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A)).left =
        (e.hom ≫ ((toUnit Q₀.A ≫ t₀) * 𝟙 Q₀.A)).left ≫ ψ₀ := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, Category.assoc,
        transl_comm hpb.1 t t₀ et, ← Category.assoc e'.inv.left, ee, Category.id_comp]
    rw [E] at j₁
    have j₂ := LBIso.chartPull (Geo.Tor.chartPullPull _ _ (e.hom.left ≫ ψ₀ ≫ e'.inv.left) rfl)
      (Geo.Tor.chartPullPull _ _ _ rfl) i'
    have j₃ := LBIso.trans P₀.isLB (pull_isLB Q₀.isLB _) (pull_isLB Q.isLB _) i₀ (lbIso_pull_comp hpb.2.2 _)
    exact LBIso.trans P₀.isLB (pull_isLB Q.isLB _) (pull_isLB Q'.isLB _) j₃
      (LBIso.trans (pull_isLB Q'.isLB _) (pull_isLB (DVR.linComb_isLB _ Q.isLB _ _) _) (pull_isLB Q.isLB _) j₂ j₁).symm
  · rw [Category.assoc, Category.assoc, ← Category.assoc e'.inv.left, ee, Category.id_comp, heφ]

theorem exists_point_lift {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_etale_sqrt (hL : Out.Laws) {K : Type} [Field K] {ζ : K} (σ : K →+* ℂ) (F : SFam h k ζ) (hk : 2 ≤ k)
    (hζ : IsUnit ζ) (p₀ : Sp ℂ ⟶ F.X) :
    ∃ (R : Type) (_ : CommRing R) (π : Sp R ⟶ F.X) (p : Sp ℂ ⟶ Sp R) (Q : Out.PolAV (Sp R))
      (φ : Q.A.left ⟶ F.univ.A.left), Etale π ∧ p ≫ π = p₀ ∧ SqOf Q F.univ π φ ∧ TorsConst Q.A 2 := by
  have := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) F.s
  have : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := F.X) (x := p₀ (default : PrimeSpectrum ℂ))
    (U := ⊤) trivial
  have : IsNoetherianRing Γ(F.X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : CharZero K := σ.charZero
  let f : Sp Γ(F.X, U) ⟶ F.X := hU.fromSpec
  have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨β, -⟩ := Spec.map_surjective (f ≫ F.s)
  letI : Algebra ℚ Γ(F.X, U) := (β.hom.comp (algebraMap ℚ K)).toAlgebra
  obtain ⟨R, _, _, Q, φ, ⟨h₁, h₂, h₃⟩, hQ, hT⟩ := GlobalTheory.T.exists_symmetric_sqrt_principal_siegel_finite_etale hL h k K ζ Γ(F.X, U) F.X F.s F.univ f hk hζ F.princ
  have : IsFinite (spMap (algebraMap Γ(F.X, U) R)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h₁)
  have : Surjective (spMap (algebraMap Γ(F.X, U) R)) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : Etale (spMap (algebraMap Γ(F.X, U) R)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.etale_algebraMap.2 h₂)
  have hr : Set.range p₀ ⊆ Set.range f := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) z default]
    exact hU.range_fromSpec.ge hp
  obtain ⟨p, hp⟩ := exists_point_lift (spMap (algebraMap Γ(F.X, U) R)) (IsOpenImmersion.lift f p₀ hr)
  exact ⟨R, _, _, p, Q, φ, inferInstance, by rw [← Category.assoc, hp, IsOpenImmersion.lift_fac], hQ, hT⟩

theorem exists_nhds_sameComp : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ₀ : Matrix (Fin h) (Fin h) ℂ) (p₀ : Sp ℂ ⟶ F.X), p₀ ≫ F.s = spMap σ → PtAt F.univ p₀ τ₀ → ∃ N ∈ nhds τ₀, ∀ τ ∈ N, ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → PtAt F.univ p τ → SameComp F.s σ p p₀ := by
  intro hL _ hU h k K _ ζ σ F hh hk ho hζ τ₀ p₀ hs ⟨P₀, lev₀, φ₀, hper, hsq, hlev⟩
  have hζ' : IsUnit ζ := IsUnit.mk0 _ fun e => Complex.exp_ne_zero _ (by rw [← hζ, e, map_zero])
  obtain ⟨R, _, π, p₁, Q₁, φ₁, het, rfl, hQ₁, hT⟩ := exists_etale_sqrt hL σ F (by omega) hζ' p₀
  obtain ⟨Q, φ, ψ, hQ, hpb, rfl⟩ := exists_sqOf_polPB hL hQ₁ hT p₁ hsq
  choose l hl hl' using fun a => exists_section_pull hQ.1 (F.univ.lev a) k (F.univ.lev_tors a)
  have := F.smooth
  have sm : SmoothOfRelativeDimension (h * (h + 1) / 2) (π ≫ F.s) := by
    have := smoothOfRelativeDimension_comp 0 (h * (h + 1) / 2) π F.s
    rwa [zero_add] at this
  have : Smooth (π ≫ F.s) := SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) _
  obtain ⟨B, y, -, -, -, -, hB, hB0, hy0, hys, hyh, hyi, -⟩ :=
    SubfieldChart.exists_holomorphic_chart K σ _ (π ≫ F.s) _ p₁ sm (by rw [← Category.assoc, hs])
  subst hy0
  obtain ⟨B₁, τ, hB₁, hB₁0, hB₁B, hτ0, hτd, hτ⟩ := PeriodLift.exists_local_period_matrix hL hU K σ _ (π ≫ F.s) Q h k _ l
    B y 0 P₀ ψ τ₀ lev₀ inferInstance (by omega) hl hB hB0 hys hyh hpb hper fun a => by
      apply hQ.1.1.hom_ext
      · rw [Category.assoc, hlev, Category.assoc, Category.assoc, hl']
      · rw [Category.assoc, hpb.1.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hpt : ∀ b ∈ B₁, PtAt F.univ (y b ≫ π) (τ b) := fun b hb => by
    obtain ⟨P, χ, lev, h₁, h₂, h₃⟩ := hτ b hb
    exact ⟨P, lev, χ ≫ φ, h₂, (sqOf_calculus h k K ζ _ _ _ F.s F.univ π).1 _ Q P φ χ hQ h₁, fun a => by
      rw [← Category.assoc, h₃, Category.assoc, hl', Category.assoc]⟩
  have hys' : ∀ b ∈ B, (y b ≫ π) ≫ F.s = spMap σ := fun b hb => by rw [Category.assoc, hys b hb]
  obtain ⟨B₂, hB₂, hB₂0, hB₂B, hinj⟩ := EtaleLocInj.exists_open_injOn _ _ π _ B y 0 het hB hB0 hyh
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hB₁.inter hB₂) 0 ⟨hB₁0, hB₂0⟩
  have hbB : Metric.ball 0 ε ⊆ B := fun b hb => hB₁B (hball hb).1
  obtain ⟨N, hN, hNτ⟩ := SiegelOpen.exists_nhds_subset_image h (Metric.ball 0 ε) τ 0 Metric.isOpen_ball
    (Metric.mem_ball_self hε) (fun i j => (hτd i j).mono fun b hb => (hball hb).1)
    (fun b hb => let ⟨_, _, _, H, _⟩ := hpt b (hball hb).1; ⟨H.2.1, H.2.2.1⟩) fun b hb b' hb' e =>
      hyi (hbB hb) (hbB hb') (hinj b (hball hb).2 b' (hball hb').2
        (GlobalTheory.T.siegelFamily_complexPoint_eq_of_same_periodMatrix hL hU h k K ζ σ F hh hk ho hζ (τ b) _ _ (hys' b (hbB hb)) (hys' b' (hbB hb'))
          (hpt b (hball hb).1) (e ▸ hpt b' (hball hb').1)))
  refine ⟨N, hτ0 ▸ hN, fun t ht p hp hpt' => ?_⟩
  have H := hpt'
  obtain ⟨_, _, _, H, _⟩ := H
  obtain ⟨b, hb, rfl⟩ := hNτ t ht H.2.1 H.2.2.1
  rw [GlobalTheory.T.siegelFamily_complexPoint_eq_of_same_periodMatrix hL hU h k K ζ σ F hh hk ho hζ (τ b) p _ hp (hys' b (hbB hb)) hpt' (hpt b (hball hb).1)]
  exact sameComp_of_isHolTo K σ _ F.s _ (Metric.ball 0 ε) (fun b => y b ≫ π) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun b hb => hys' b (hbB hb))
    (LocLift.isHolTo_comp_hom (LocLift.isHolTo_mono hyh Metric.isOpen_ball hbB) π) b hb 0 (Metric.mem_ball_self hε)

end GlobalTheory.SiegelNearby
end
end
