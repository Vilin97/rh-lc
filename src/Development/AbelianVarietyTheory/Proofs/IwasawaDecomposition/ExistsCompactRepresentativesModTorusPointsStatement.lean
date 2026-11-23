module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPerHolOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowPointIntegralPadicGroupScheme
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Mathlib.Order.Filter.FilterProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Basify
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Topology Filter TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Points

namespace GlobalTheory.ProperPoints

section Ultrapower

variable {I F : Type} [NormedField F] (𝒰 : Ultrafilter I)

def bddRing (F : Type) [NormedField F] : ValuationSubring ((𝒰 : Filter I).Germ F) where
  carrier := {a | ∃ (M : ℝ) (f : I → F), a = (f : (𝒰 : Filter I).Germ F) ∧ ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ M}
  mul_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M * N, f * g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  one_mem' := ⟨1, 1, rfl, Eventually.of_forall fun i => by simp⟩
  add_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M + N, f + g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  zero_mem' := ⟨0, 0, rfl, Eventually.of_forall fun i => by simp⟩
  neg_mem' := by
    rintro _ ⟨M, f, rfl, hf⟩
    refine ⟨M, -f, rfl, ?_⟩
    filter_upwards [hf] with i h1
    simpa using h1
  mem_or_inv_mem' := by
    intro a
    induction a using Germ.inductionOn with
    | h f =>
      by_cases h : ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ 1
      · exact Or.inl ⟨1, f, rfl, h⟩
      · refine Or.inr ⟨1, f⁻¹, rfl, ?_⟩
        filter_upwards [Ultrafilter.eventually_not.2 h] with i hi
        rw [Pi.inv_apply, norm_inv]
        exact inv_le_one_of_one_le₀ (not_le.1 hi).le

def constBdd (F : Type) [NormedField F] : F →+* bddRing 𝒰 F where
  toFun a := ⟨((fun _ => a : I → F) : (𝒰 : Filter I).Germ F), ‖a‖, _, rfl, Eventually.of_forall fun _ => le_rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable [ProperSpace F]

theorem exists_tendsto (a : bddRing 𝒰 F) : ∃ c : F, (a : (𝒰 : Filter I).Germ F).Tendsto (𝓝 c) := by
  obtain ⟨_, M, f, rfl, hf⟩ := a
  obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : F) M).ultrafilter_le_nhds (𝒰.map f) (by
    rw [le_principal_iff]
    exact hf.mono fun i hi => by simpa using hi)
  exact ⟨c, hc⟩

theorem tendsto_choose (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (exists_tendsto 𝒰 a).choose) := by
  have h := (exists_tendsto 𝒰 a).choose_spec
  generalize (exists_tendsto 𝒰 a).choose = c at h ⊢
  rwa [hf] at h

theorem choose_eq (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) {c : F}
    (hc : Tendsto f 𝒰 (𝓝 c)) : (exists_tendsto 𝒰 a).choose = c :=
  tendsto_nhds_unique (tendsto_choose 𝒰 a f hf) hc

def stdPart (F : Type) [NormedField F] [ProperSpace F] : bddRing 𝒰 F →+* F where
  toFun a := (exists_tendsto 𝒰 a).choose
  map_one' := choose_eq 𝒰 1 (fun _ => 1) rfl tendsto_const_nhds
  map_zero' := choose_eq 𝒰 0 (fun _ => 0) rfl tendsto_const_nhds
  map_mul' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f * g) (by rw [Germ.coe_mul, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).mul (tendsto_choose 𝒰 b g hg))
  map_add' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f + g) (by rw [Germ.coe_add, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).add (tendsto_choose 𝒰 b g hg))

theorem tendsto_stdPart (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (stdPart 𝒰 F a)) := tendsto_choose 𝒰 a f hf

theorem stdPart_constBdd (a : F) : stdPart 𝒰 F (constBdd 𝒰 F a) = a :=
  choose_eq 𝒰 _ (fun _ => a) rfl tendsto_const_nhds

end Ultrapower

theorem valR_mul_pow {C : Type} [CommRing C] {X : Scheme.{0}} {U V : X.Opens} (h : Γ(X, U))
    (hV : X.basicOpen h ≤ V) (f : Γ(X, V)) (n : ℕ) (a : Γ(X, U))
    (ha : (X.presheaf.map (homOfLE hV).op).hom f * algebraMap Γ(X, U) Γ(X, X.basicOpen h) h ^ n =
      algebraMap Γ(X, U) Γ(X, X.basicOpen h) a)
    (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ X.basicOpen h) : valR y V f * valR y U h ^ n = valR y U a := by
  have h1 := congrArg (valR y (X.basicOpen h)) ha
  rw [valR_mul y _ hy, valR_pow y _ hy, valR_res y hV hy] at h1
  have h2 : ∀ t : Γ(X, U), valR y (X.basicOpen h) (algebraMap Γ(X, U) Γ(X, X.basicOpen h) t) =
      valR y U t := fun t => valR_res y (X.basicOpen_le h) hy t
  rwa [h2, h2] at h1

section Limit

variable {I F : Type} [Field F] (𝒰 : Ultrafilter I) {X : Scheme.{0}} (e : I → (Sp F ⟶ X)) {U : X.Opens}

def germVal (hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U) : Γ(X, U) →+* (𝒰 : Filter I).Germ F where
  toFun f := ((fun i => valR (e i) U f : I → F) : (𝒰 : Filter I).Germ F)
  map_one' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_one _ U hi)
  map_mul' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_mul _ U hi f g)
  map_zero' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_zero _ U hi)
  map_add' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_add _ U hi f g)

theorem exists_germPoint [CompactSpace X] : ∃ ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X, ∀ V : X.Opens, ⊤ ≤ ξ ⁻¹ᵁ V →
    (∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ V) ∧
      ∀ f : Γ(X, V), valR ξ V f = ((fun i => valR (e i) V f : I → F) : (𝒰 : Filter I).Germ F) := by
  obtain ⟨z, hz⟩ : ∃ z : X, Tendsto (fun i => e i (IsLocalRing.closedPoint F)) 𝒰 (𝓝 z) :=
    ⟨_, (𝒰.map fun i => e i (IsLocalRing.closedPoint F)).le_nhds_lim⟩
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  have hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U :=
    (hz.eventually (U.isOpen.mem_nhds hzU)).mono fun i hi => (le_preimage_iff _ _).2 hi
  let ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X := Spec.map (CommRingCat.ofHom (germVal 𝒰 e hl)) ≫ hU.fromSpec
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := le_preimage_specMap_fromSpec hU _
  have hval : ∀ f, valR ξ U f = germVal 𝒰 e hl f := fun f => by
    rw [valR_eq ξ U hξ, valMap_specMap_fromSpec]
    rfl
  refine ⟨ξ, fun V hV => ?_⟩
  obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, (le_preimage_iff ξ V).1 hV⟩
    ((le_preimage_iff ξ U).1 hξ)
  have hξh : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen h := (le_preimage_iff ξ _).2 hh
  have hne : germVal 𝒰 e hl h ≠ 0 := by
    rw [← hval]
    exact ((le_preimage_basicOpen_iff ξ hξ h).1 hξh).ne_zero
  have hl' : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ X.basicOpen h := by
    have h0 : ¬ ∀ᶠ i in (𝒰 : Filter I), valR (e i) U h = 0 := fun h0 => hne (Germ.coe_eq.2 h0)
    filter_upwards [hl, Ultrafilter.eventually_not.2 h0] with i h1 h2
      using (le_preimage_basicOpen_iff _ h1 h).2 (Ne.isUnit h2)
  refine ⟨hl'.mono fun i hi => le_preimage_mono _ hhV hi, fun f => ?_⟩
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((X.presheaf.map (homOfLE hhV).op).hom f)
  have h1 := valR_mul_pow h hhV f n a ha ξ hξh
  rw [hval, hval] at h1
  apply mul_right_cancel₀ (pow_ne_zero n hne)
  rw [h1, ← map_pow]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hl, hl'] with i h2 h3
  have := valR_mul_pow h hhV f n a ha (e i) h3
  rw [← valR_pow _ _ h2] at this
  exact this.symm

end Limit

theorem compactSpace_pts {F : Type} [NormedField F] [ProperSpace F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    [UniversallyClosed p] : CompactSpace (Pts p) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 _ => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_germPoint 𝒰 (fun x : Pts p => x.1)
  have hE : ValuativeCriterion.Existence p :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed p) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) p).1
  have hw : ξ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F))) ≫
      spMap (constBdd 𝒰 F) := by
    rw [← Spec.map_comp, ← Spec.map_preimage (ξ ≫ p)]
    congr 1
    ext a
    refine (valR_constFn p ξ ⊤ (le_preimage_top _) a).symm.trans ?_
    rw [(hξ ⊤ (le_preimage_top _)).2]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => valR_constFn_of_section p x.1 x.2 ⊤ (le_preimage_top _) a)
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Sp (bddRing 𝒰 F) ⟶ X,
      spMap (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F)) ≫ l = ξ ∧ l ≫ p = spMap (constBdd 𝒰 F) := by
    obtain ⟨⟨l, hl, hl'⟩⟩ := (hE
      { R := bddRing 𝒰 F, K := (𝒰 : Filter (Pts p)).Germ F, i₁ := ξ, i₂ := spMap (constBdd 𝒰 F),
        commSq := ⟨hw⟩ }).exists_lift
    exact ⟨l, hl, hl'⟩
  have hx : (spMap (stdPart 𝒰 F) ≫ l) ≫ p = 𝟙 _ := by
    rw [Category.assoc, hl₂, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact stdPart_constBdd 𝒰 a
  refine ⟨⟨_, hx⟩, trivial, ?_⟩
  obtain ⟨V, hV, hlV, -⟩ := exists_isAffineOpen_le (C := bddRing 𝒰 F) l (le_preimage_top _)
  have hξV : ⊤ ≤ ξ ⁻¹ᵁ V := hl₁ ▸ le_preimage_comp _ l hlV (le_preimage_top _)
  have H : Tendsto (fun x : Pts p => x.1) 𝒰 (𝓝 (spMap (stdPart 𝒰 F) ≫ l)) := by
    refine tendsto_of_isAffineOpen hV (le_preimage_comp _ l hlV (le_preimage_top _)) (hξ V hξV).1 fun f => ?_
    rw [valR_spMap_comp _ l V hlV]
    refine tendsto_stdPart 𝒰 _ _ ?_
    rw [← (hξ V hξV).2, ← hl₁, valR_spMap_comp _ l V hlV]
    rfl
  exact tendsto_id'.1 (tendsto_subtype_rng.2 H)

end GlobalTheory.ProperPoints
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPoints

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.BdArc
  Filter Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan GlobalTheory.Points GlobalTheory.IntegralPower

namespace GlobalTheory.TorusCocompact

theorem exists_isCompact_surjOn {V H : Type} [NormedAddCommGroup V] [ProperSpace V] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] (φ : V → H) (hφ : ∀ z w, φ (z + w) = φ z * φ w)
    (hs : Function.Surjective φ) (hc : Continuous φ) : ∃ C : Set V, IsCompact C ∧ ∀ z, ∃ c ∈ C, φ (z - c) = 1 := by
  let ψ : V →+ Additive H := AddMonoidHom.mk' (fun z => Additive.ofMul (φ z)) hφ
  have : BaireSpace (Additive H) := inferInstanceAs (BaireSpace H)
  have : T2Space (Additive H) := inferInstanceAs (T2Space H)
  have ho : IsOpenMap φ := AddMonoidHom.isOpenMap_of_sigmaCompact ψ hs hc
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover (fun n : ℕ => φ '' Metric.ball 0 n)
    (fun n => ho _ Metric.isOpen_ball) (fun h _ => by
      obtain ⟨z, rfl⟩ := hs h
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨n, z, by simpa using hn, rfl⟩)
    (Monotone.directed_le fun m n h => Set.image_mono (Metric.ball_subset_ball (Nat.cast_le.2 h)))
  refine ⟨Metric.closedBall 0 n, isCompact_closedBall _ _, fun z => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hn (Set.mem_univ (φ z))
  refine ⟨c, Metric.ball_subset_closedBall hc, ?_⟩
  have h := hφ (z - c) c
  rw [sub_add_cancel, hcz] at h
  exact (mul_eq_right.1 h.symm)

theorem exists_lift_point {A B : Over (Sp ℂ)} (q : A ⟶ B) [Surjective q.left] [LocallyOfFiniteType q.left]
    (w : Over.mk (𝟙 (Sp ℂ)) ⟶ B) : ∃ u : Over.mk (𝟙 (Sp ℂ)) ⟶ A, u ≫ q = w := by
  let w' : Sp ℂ ⟶ B.left := w.left
  obtain ⟨z, -⟩ := (pullback.snd q.left w').surjective (IsLocalRing.closedPoint ℂ)
  obtain ⟨x, hx, -⟩ := GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd q.left w') isClosed_univ.isLocallyClosed
    ⟨z, trivial⟩
  have h : (x ≫ pullback.fst q.left w') ≫ q.left = w' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  refine ⟨Over.homMk (x ≫ pullback.fst q.left w') ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w q, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h).trans (Over.w w)

section Fibre

variable {X : Scheme.{0}} {G : Over X} {y : Sp ℂ ⟶ X}

def fibrePt (x : Over.mk y ⟶ G) : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G :=
  Over.homMk (pullback.lift x.left (𝟙 (Sp ℂ)) ((Over.w x).trans (Category.id_comp y).symm))
    (pullback.lift_snd _ _ _)

theorem fibrePt_fst (x : Over.mk y ⟶ G) : (fibrePt x).left ≫ pullback.fst G.hom y = x.left :=
  pullback.lift_fst _ _ _

theorem fibre_ext {u v : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G}
    (h : u.left ≫ pullback.fst G.hom y = v.left ≫ pullback.fst G.hom y) : u = v :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem fibrePt_surjective : Function.Surjective (fibrePt (G := G) (y := y)) := fun u =>
  ⟨Over.homMk (u.left ≫ pullback.fst G.hom y) (by
    have h : u.left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w u
    rw [Category.assoc, pullback.condition, reassoc_of% h]
    rfl), fibre_ext (fibrePt_fst _)⟩

theorem fibrePt_mul [GrpObj G] (a b : Over.mk y ⟶ G) : fibrePt (a * b) = fibrePt a * fibrePt b := by
  let U : Over.mk ((Over.mk (𝟙 (Sp ℂ))).hom ≫ y) ⟶ Over.mk y := Over.homMk (𝟙 (Sp ℂ)) rfl
  have hU : ∀ x : Over.mk y ⟶ G, (U ≫ x).left = x.left := fun x => Category.id_comp _
  refine fibre_ext ?_
  rw [fibrePt_fst, ← (isGrpPullback_pullback G y).2 _ (fibrePt a) (fibrePt b) (U ≫ a) (U ≫ b)
    ((hU a).trans (fibrePt_fst a).symm) ((hU b).trans (fibrePt_fst b).symm), ← comp_mul, hU]

theorem continuous_fibrePt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (e : V → (Over.mk y ⟶ G))
    (he : IsHolTo Set.univ (fun z => (e z).left)) :
    Continuous fun z => leftPt (𝟙 (Sp ℂ)) (fibrePt (e z)) := by
  have h1 : Continuous fun z => leftPt y (e z) := by
    refine GlobalTheory.Points.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · simpa using (he U 0).1
    · exact (he U f).2.continuousOn.mono fun _ hb => ⟨trivial, hb⟩
  refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom y)).continuous_iff.2 ?_
  refine (h1.prodMk (continuous_const (y := 𝟙 (Sp ℂ)))).congr fun z => ?_
  exact Prod.ext (fibrePt_fst (e z)).symm (Over.w (fibrePt (e z))).symm

end Fibre


attribute [local instance] ptTopology in
theorem exists_isCompact_mod_torusPts : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G →
    (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) →
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) →
    ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  intro X G _ y g e E hG hadd hsurj hhol _
  let := E.addCommGroup
  let := E.grpB
  have := E.q_hom
  have := E.q_surjective
  have := E.isAbelian.proper
  have := hG.smooth
  have : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by
    rw [Over.w E.q]
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom y))
  have : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  have : CompactSpace (PtsOver E.B.hom (𝟙 (Sp ℂ))) := GlobalTheory.ProperPoints.compactSpace_pts E.B.hom
  have := compactSpace_of_ptsOver (𝟙 (Sp ℂ)) E.B
  have : IsTopologicalGroup (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) := by
    exact { continuous_mul := (continuous_comp_over _ (μ[E.B])).comp (continuous_lift _ E.B E.B)
            continuous_inv := continuous_comp_over _ (GrpObj.inv (X := E.B)) }
  have : T2Space (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) :=
    have := PtsOver.t2Space E.B.hom (𝟙 (Sp ℂ))
    T2Space.of_injective_continuous (f := fun x => (⟨x.left, Over.w x⟩ : PtsOver E.B.hom (𝟙 (Sp ℂ))))
      (fun _ _ h => Over.OverMorphism.ext (congrArg Subtype.val h))
      ((isEmbedding_leftPt (𝟙 (Sp ℂ)) E.B).continuous.subtype_mk _)
  obtain ⟨C, hC, H⟩ := exists_isCompact_surjOn (fun z => fibrePt (e z) ≫ E.q)
    (fun z w => by rw [hadd, fibrePt_mul, mul_comp])
    (fun w => by
      obtain ⟨u, rfl⟩ := exists_lift_point E.q w
      obtain ⟨x, rfl⟩ := fibrePt_surjective u
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, rfl⟩)
    ((continuous_comp_over _ E.q).comp ((isEmbedding_leftPt _ _).continuous_iff.2 (continuous_fibrePt e hhol)))
  refine ⟨C, hC, fun z => ?_⟩
  obtain ⟨c, hc, hz⟩ := H z
  refine ⟨c, hc, E.isKernel.lift (fibrePt (e (z - c))) (toUnit _) hz, ?_⟩
  rw [IsPullback.lift_fst]
  exact fibrePt_fst _

end GlobalTheory.TorusCocompact
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan

theorem _root_.GlobalTheory.T.exists_compact_representatives_mod_torusPoints : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) → (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) → ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  first | exact @GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts | exact GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts | (intros; apply GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts <;> assumption)
end
end
