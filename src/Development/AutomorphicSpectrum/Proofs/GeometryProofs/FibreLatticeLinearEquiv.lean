module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDiffUniqueStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearLift
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDimEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.UnifDim

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

theorem eq_of_linear_lift {M : Type*} [Group M] {g d : ℕ} (e : (Fin g → ℂ) → M)
    (e' : (Fin d → ℂ) → M) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hon : Function.Surjective e) (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin d → ℂ))
    (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hk' : ∀ z, e' z = 1 ↔ z ∈ Λ')
    [DiscreteTopology Λ] [DiscreteTopology Λ']
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (hF : ∀ z, e' (F z) = e z) : g = d := by
  have hinj := AnyUnif.injective_of_ker_le_discrete Λ F fun z hz => by
    rw [← hk, ← hF, hz]
    exact (hk' 0).2 Λ'.zero_mem
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete Λ' _ fun w => by
    obtain ⟨z, hz⟩ := hon (e' w)
    refine ⟨⟨w - F z, (hk' _).1 ?_⟩, z, by simp⟩
    have h := he' (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem holOn_ex (u : HolUnif A L g) : HolOn Set.univ u.ex := fun U f => by
  simpa only [Set.mem_univ, true_and] using u.hol U f

theorem compactSpace_points (u : HolUnif A L g) : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := by
  have hc : Continuous u.ex :=
    continuous_iff_continuousAt.2 fun z => (holOn_ex u).continuousAt (Set.mem_univ z)
  haveI := u.discrete
  haveI := holUnif_isZLattice u
  haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ
  haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (ZSpan.fundamentalDomain_isBounded b).closure
  refine isCompact_univ_iff.1 ((hK.image hc).of_isClosed_subset isClosed_univ fun x _ => ?_)
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
  have hm : ((ZSpan.floor b z : _) : Fin g → ℂ) ∈ u.Λ := by
    have e := Module.Basis.ofZLatticeBasis_span ℝ u.Λ (Module.Free.chooseBasis ℤ u.Λ)
    exact e.le (ZSpan.floor b z).2
  have h := u.ex_add (ZSpan.fract b z) (ZSpan.floor b z)
  rw [(u.ker _).2 hm, _root_.mul_one, ZSpan.fract_apply, sub_add_cancel] at h
  rw [ZSpan.fract_apply]
  exact h.symm

theorem eq_relativeDimension : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ)
    (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  intro A _ L g d u hd
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := htop A
  have := compactSpace_points u
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A d hd 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin d → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hu := holOn_ex u
  have hu0 : u.ex 0 = 1 := holUnif_ex_zero_eq_one u
  have h1 : φ (u.ex 0) = 0 := by rw [hu0]; exact hφ.map_zero
  have h2 : AnalyticAt ℂ (fun w => φ (u.ex w)) 0 :=
    hu.analyticAt t (Set.mem_univ _) (hu0 ▸ hU1)
  have hG0 : hφ.log (φ (u.ex 0)) = 0 := by
    simp only [h1]
    exact hφ.isLocalCommGroupLaw.log_zero
  have hGa : AnalyticAt ℂ (fun w => hφ.log (φ (u.ex w))) 0 :=
    AnalyticAt.comp (g := hφ.log) (h1 ▸ hφ.isLocalCommGroupLaw.analyticAt_log) h2
  have hGe : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (hφ.exp (hφ.log (φ (u.ex w)))).toMul = u.ex w := by
    have h3 : Tendsto u.ex (𝓝 0) (𝓝 1) := hu0 ▸ (hu.continuousAt (Set.mem_univ 0)).tendsto
    exact h3.eventually hφ.exp_log
  have hF := EndoLinear.fderiv_lifts (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) hφ.periodLattice (fun z => Iff.rfl)
    inferInstance u.ex u.ex_add _ hG0 hGa.differentiableAt hGe
  haveI := u.discrete
  exact eq_of_linear_lift u.ex (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) u.ex_onto u.Λ hφ.periodLattice u.ker
    (fun z => Iff.rfl) (fderiv ℂ (fun w => hφ.log (φ (u.ex w))) 0).toLinearMap hF

end GlobalTheory.CompanionTheory.Ar.UnifDim
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDimEqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.holomorphic_uniformization_dim_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | exact GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | (intros; apply GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquiv

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique

theorem dim_eq_of_smooth {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g d : ℕ} (u : HolUnif A L g)
    (hs : SmoothOfRelativeDimension d A.hom) : g = d :=
  GlobalTheory.T.holomorphic_uniformization_dim_eq A L g d u hs

theorem isDiff_unique_off {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (hs : SmoothOfRelativeDimension g A.hom) (hc : ConnectedSpace A.left) {v : epsR ℂ ⟶ A} (hv : ¬ IsTangent v)
    {w w' : Fin g → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' :=
  GlobalTheory.T.holomorphic_uniformization_diff_unique A L g u hs hc v hv w w' h h'


open TangentOrigin in
theorem exists_linear_of_smooth {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
    (hs : SmoothOfRelativeDimension g A.hom) (u₀ u : HolUnif A L g) :
    ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u₀.ex z := by
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u hs
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u₀.ex z)) u₀.ex_add
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q ↦
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z ↦ u.ker z
  have key : ∃! F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, ex (F z) = G' z := by
   refine existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    ?_ ?_ (u.hol U 0).1 (u₀.hol U 0).1 (fun s ↦ (u.hol U s).2) (fun s ↦ (u₀.hol U s).2) ?_
   · rw [← map_zero ex]
     exact h0
   · intro a ha b hb h
     refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
       (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦ ?_))
     exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))
   · intro w hw
     obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
     have hvU := (tangent_mem_iff (u := u) hv U).2 h0
     refine (h₁ v hv).unique hd ((isDiff_iff hv hU hvU h0 0).2 ?_)
     rw [(isDiff_iff hv hU hvU h0 w).1 hd]
     refine RingHom.ext fun s ↦ TrivSqZeroExt.ext rfl ?_
     rw [jet_snd, jet_snd, map_zero]
     exact hw s
  obtain ⟨F, hF, -⟩ := key
  exact ⟨F, hF⟩


open GlobalTheory.OrthoMetric in
theorem exists_transport {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : Sp ℂ ⟶ X} {A A' : Over (Sp ℂ)} [GrpObj A]
    [GrpObj A'] {φ : A.left ⟶ G.left} {φ' : A'.left ⟶ G.left} (hp : IsGrpPullback A G y φ)
    (hp' : IsGrpPullback A' G y φ') {L : LB G.left} {g : ℕ} (u' : HolUnif A' (L.pull φ') g) :
    ∃ u : HolUnif A (L.pull φ) g, (∀ z, (u.ex z).left ≫ φ = (u'.ex z).left ≫ φ') ∧ (∀ z, z ∈ u.Λ ↔ z ∈ u'.Λ) ∧
      ∀ (j : L.ι) z, u.fr (fun _ => j) z = u'.fr (fun _ => j) z := by
  let e : (Fin g → ℂ) → (Over.mk y ⟶ G) := fun z => Function.surjInv (liftPt_surjective hp') (u'.ex z)
  have he : ∀ z, liftPt hp' (e z) = u'.ex z := fun z => Function.surjInv_eq _ _
  have hel : ∀ z, (e z).left = (u'.ex z).left ≫ φ' := fun z => by
    rw [← he, liftPt_comp]
  have hpre : ∀ z (V : G.left.Opens), ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ' ⁻¹ᵁ V) ↔ ⊤ ≤ (e z).left ⁻¹ᵁ V := fun z V => by
    rw [hel]
    exact (GlobalTheory.top_le_preimage_comp _ _ _).symm
  have hj : ∀ (j : L.ι) z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull φ').U (fun _ => j) ↔ ⊤ ≤ (e z).left ⁻¹ᵁ L.U j :=
    fun j z => by
      rw [← he z]
      exact lift_le hp' (e z) (fun _ => j)
  refine ⟨fibreUnif hp e u'.Λ.toAddSubgroup (fun j => u'.fr (fun _ => j)) ?_ ?_ ?_ u'.discrete u'.full ?_ ?_ ?_ ?_,
    fun z => liftPt_comp hp _ |>.trans (hel z), fun z => Iff.rfl, fun j z => rfl⟩
  · intro z w
    refine liftPt_injective hp' ?_
    rw [liftPt_mul, he, he, he, u'.ex_add]
  · intro p
    obtain ⟨z, hz⟩ := u'.ex_onto (liftPt hp' p)
    exact ⟨z, liftPt_injective hp' ((he z).trans hz)⟩
  · intro z
    have h1 : e z = 1 ↔ u'.ex z = 1 := by
      rw [← he z, ← liftPt_one hp']
      exact (liftPt_injective hp').eq_iff.symm
    exact h1.trans (u'.ker z)
  · intro V f
    have h := u'.hol (φ' ⁻¹ᵁ V) ((φ'.app V).hom f)
    have es : {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e b).left ⁻¹ᵁ V} = {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ' ⁻¹ᵁ V)} :=
      Set.ext fun z => ⟨fun h => (hpre z V).2 h.2, fun h => ⟨trivial, (hpre z V).1 h⟩⟩
    rw [es]
    refine ⟨h.1, h.2.congr fun z _ => ?_⟩
    show valAt' (e z).left V f = _
    rw [hel]
    exact (GlobalTheory.valAt'_comp _ _ _ _).symm
  · intro j
    have es : {z | ⊤ ≤ (e z).left ⁻¹ᵁ L.U j} = {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull φ').U (fun _ => j)} :=
      Set.ext fun z => (hj j z).symm
    rw [es]
    exact u'.fr_hol _
  · intro j z hz
    exact u'.fr_ne _ z ((hj j z).2 hz)
  · intro j j' z hz
    obtain ⟨h1, h2⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
    have hz' := (GlobalTheory.top_le_preimage_inf (u'.ex z).left _ _).2 ⟨(hj j z).2 h1, (hj j' z).2 h2⟩
    rw [u'.fr_compat _ _ z hz', GlobalTheory.ArchMetricCompare.val_pull_g L _ _ _ _ hz', hel]

theorem isDiff_of_comp {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g : ℕ}
    (u : HolUnif A L g) (u' : HolUnif A' L' g) (ψ : A'.left ⟶ A.left)
    (hex : ∀ w, (u'.ex w).left ≫ ψ = (u.ex w).left) {w : Fin g → ℂ} {v₁ : epsR ℂ ⟶ A} {v₂ : epsR ℂ ⟶ A'}
    (h : v₂.left ≫ ψ = v₁.left) (d : u'.IsDiff w v₂) : u.IsDiff w v₁ := by
  intro U hU f
  have hU' : ⊤ ≤ v₂.left ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h]
    exact hU
  have k := d (ψ ⁻¹ᵁ U) hU' ((ψ.app U).hom f)
  have aux : ∀ (q : (epsR ℂ).left ⟶ A.left) (_ : v₂.left ≫ ψ = q) (hq : ⊤ ≤ q ⁻¹ᵁ U),
      (q.appLE U ⊤ hq).hom f = (v₂.left.appLE (ψ ⁻¹ᵁ U) ⊤ hU').hom ((ψ.app U).hom f) := by
    intro q e hq
    subst e
    rw [Scheme.Hom.comp_appLE]
    rfl
  have e2 : (fun z => valAt' (u'.ex z).left (ψ ⁻¹ᵁ U) ((ψ.app U).hom f)) = fun z => valAt' (u.ex z).left U f := by
    funext z
    rw [GlobalTheory.valAt'_comp, hex]
  rw [e2] at k
  rw [aux _ h hU]
  exact k

theorem isDiff_unique {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (hs : SmoothOfRelativeDimension g A.hom) (hc : ConnectedSpace A.left) {v : epsR ℂ ⟶ A}
    {w w' : Fin g → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' := by
  by_cases hv : IsTangent v
  · exact ((TorusTransfer.tangent_bijective u hs).1 v hv).unique h h'
  · exact isDiff_unique_off u hs hc hv h h'


open GlobalTheory.OrthoMetric in
theorem exists_linearEquiv_of_fibreLatVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Sp ℂ ⟶ X) (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (A₀ : Type) (x : A₀ → Fin g → ℂ) (x' : A₀ → Fin g' → ℂ) (v : A₀ → (epsAt z ⟶ t.G)), FibreLatVec t z R x v → FibreLatVec t z R' x' v → ∃ φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ), φ '' Set.range R.P = Set.range R'.P ∧ (∀ p q, R'.ip (φ p) (φ q) = R.ip p q) ∧ (∀ a p, φ (R.B a p) = R'.B a (φ p)) ∧ ∀ i, φ (x i) = x' i := by
  intro E _ _ _ H X t z g g' Λ Λ' _ _ _ _ R R' A₀ x x' v h h'
  obtain ⟨A, _, φ, u, χ, hp, hAH, hB, -, hΛ, hv⟩ := h
  obtain ⟨A', _, φ', u', χ', hp', hAH', hB', -, hΛ', hv'⟩ := h'
  have := t.semi.smooth
  have := t.semi.geomConnected
  have sm : Smooth A.hom := MorphismProperty.of_isPullback hp.1 ‹_›
  have hc : ConnectedSpace A.left := GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) z _ _ hp.1
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected A.hom (Classical.arbitrary _)
  obtain ⟨u₂, h₁, h₂, h₃⟩ := exists_transport hp hp' u'
  have e1 := dim_eq_of_smooth u hd
  have e2 := dim_eq_of_smooth u₂ hd
  subst e1
  subst e2
  have hL : (t.PP.L.pull φ).IsLB := pull_isLB t.PP.isLB φ
  obtain ⟨F, hF⟩ := exists_linear_of_smooth hd u u₂
  have hinj := UnifCompare.injective u u₂ F hF
  let T := LinearEquiv.ofInjectiveEndo F hinj
  have hTF : ∀ w, T w = F w := fun _ => rfl
  let χ₂ : u₂.Λ → ℂ := fun l => χ' ⟨l, (h₂ l).1 l.2⟩
  have hpre : ∀ (j : (t.PP.L.pull φ).ι) w, ⊤ ≤ (u₂.ex w).left ⁻¹ᵁ (t.PP.L.pull φ).U j →
      ⊤ ≤ (u'.ex w).left ⁻¹ᵁ (t.PP.L.pull φ').U j := fun j w hw => by
    have a := (GlobalTheory.ArchMetricCompare.le_pull_iff t.PP.L φ (show Sp ℂ ⟶ _ from (u₂.ex w).left) j).1 hw
    have b : (show Sp ℂ ⟶ _ from (u₂.ex w).left) ≫ φ = (show Sp ℂ ⟶ _ from (u'.ex w).left) ≫ φ' := h₁ w
    rw [b] at a
    exact (GlobalTheory.ArchMetricCompare.le_pull_iff t.PP.L φ' (show Sp ℂ ⟶ _ from (u'.ex w).left) j).2 a
  have e3 : ∀ (j : (t.PP.L.pull φ).ι) w, u₂.fr j w = u'.fr j w := fun j w => h₃ (j PUnit.unit) w
  have hAH₂ : u₂.IsAH R'.Hm χ₂ := by
    refine ⟨hAH'.1, hAH'.2.1, fun l => hAH'.2.2.1 _, fun l j w hw => ?_⟩
    rw [e3, e3]
    exact hAH'.2.2.2 ⟨l, (h₂ l).1 l.2⟩ j w (hpre j w hw)
  have hH := UnifCompare.hermForm_eq hL u u₂ hAH hAH₂ F hF
  refine ⟨T, ?_, fun p q => hH q p, fun a p => ?_, fun i => ?_⟩
  · ext y
    constructor
    · rintro ⟨w, ⟨l, rfl⟩, rfl⟩
      exact (hΛ' _).1 ((h₂ _).1 ((UnifCompare.mem_iff u u₂ F hF _).2 ((hΛ _).2 ⟨l, rfl⟩)))
    · intro hy
      have e4 : F (T.symm y) = y := T.apply_symm_apply y
      refine ⟨T.symm y, (hΛ _).1 ((UnifCompare.mem_iff u u₂ F hF _).1 ?_), T.apply_symm_apply y⟩
      rw [e4]
      exact (h₂ _).2 ((hΛ' _).2 hy)
  · have key : ∀ q, F (R.B a q) - R'.B a (F q) ∈ u₂.Λ := fun q => by
      have e : u₂.ex (F (R.B a q)) = u₂.ex (R'.B a (F q)) := by
        rw [hF]
        refine pt_ext hp ?_
        calc (u.ex (R.B a q)).left ≫ φ = (u.ex q).left ≫ φ ≫ (t.act.act a).left := hB a q
          _ = ((u.ex q).left ≫ φ) ≫ (t.act.act a).left := (Category.assoc _ _ _).symm
          _ = ((u'.ex (F q)).left ≫ φ') ≫ (t.act.act a).left := by rw [← h₁ (F q), hF]
          _ = (u'.ex (F q)).left ≫ φ' ≫ (t.act.act a).left := Category.assoc _ _ _
          _ = (u'.ex (R'.B a (F q))).left ≫ φ' := (hB' a (F q)).symm
          _ = (u₂.ex (R'.B a (F q))).left ≫ φ := (h₁ _).symm
      rw [← u₂.ker]
      have h5 := u₂.ex_add (F (R.B a q) - R'.B a (F q)) (R'.B a (F q))
      rw [sub_add_cancel, e] at h5
      exact mul_eq_right.1 h5.symm
    have h0 := GlobalTheory.LatticeHom.eq_zero_of_forall_smul_mem u₂.Λ u₂.discrete
      (z := F (R.B a p) - R'.B a (F p)) fun c => by
        have := key (c • p)
        simpa only [map_smul, smul_sub] using this
    exact sub_eq_zero.1 h0
  · obtain ⟨v₁, f₁, d₁⟩ := hv i
    obtain ⟨v₂, f₂, d₂⟩ := hv' i
    have d₃ : u₂.IsDiff (T (x i)) v₁ :=
      (UnifCompare.isDiff_iff u u₂ T.toContinuousLinearEquiv hF (x i) v₁).1 d₁
    obtain ⟨ψ, hψ⟩ := GlobalTheory.SharpPull.exists_lift hp' hp (𝟙 t.G)
    have hψ' : ψ.left ≫ φ = φ' := hψ.trans (Category.comp_id _)
    have hv₁ : v₂.left ≫ ψ.left = v₁.left := hp.1.hom_ext
      (by rw [Category.assoc, hψ', f₂, f₁]) (by rw [Category.assoc, Over.w, Over.w, Over.w])
    have hex : ∀ w, (u'.ex w).left ≫ ψ.left = (u₂.ex w).left := fun w => hp.1.hom_ext
      (by rw [Category.assoc, hψ', h₁]) (by rw [Category.assoc, Over.w, Over.w, Over.w])
    exact isDiff_unique u₂ hd hc d₃ (isDiff_of_comp u₂ u' ψ.left hex hv₁ d₂)

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique
end
end
end
