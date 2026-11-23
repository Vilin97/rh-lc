module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicBaseChangeRealPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRealPartInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfDegreeBounded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfSubgroupBounded
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepDimensionBounded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AltChainOfPermSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BddFixOfBoundedComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BoundedComplexOfBoundedSimplicialComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingFixedPointsEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyBoundedEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologySumBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CoindRetractOfFiniteIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactBaseIntegralToComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactCOfOfExactBase
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCMExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExtVanishingOfResolutionEndo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedOrbitsFiniteRepresentatives
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GoodRealFormOfRealPartOfRealInvolution
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalOrbitRepresentatives
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalVectorStabilizerProperty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbReOfMinimalVectorStabilizer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermSplitFinSucc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermutationModuleHomologyRank
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PinsOfClosedSubgroupPadicCharacterInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SimpSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Spanpsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealStructureActionOfRealInvolution
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepHomAlternatingSumEqZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepResolutionExists

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedCommOfBoundedEquiv

section

@[expose] public section

theorem UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv → UpperTheory.V.Af.BA.BddSub → UpperTheory.V.Af.BA.BddOver → UpperTheory.V.Af.BA.BddComm := by
  intro hEq hSub hOver G _ Γ Λ hc hΛ
  obtain ⟨h1, h2⟩ := hc
  have f1 : (Γ.subgroupOf Λ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h1
  have f2 : (Λ.subgroupOf Γ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h2
  have b1 := hSub Λ (Γ.subgroupOf Λ) f1 hΛ
  have e : (Γ.subgroupOf Λ) ≃* (Λ.subgroupOf Γ) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have b2 := hEq _ _ ⟨e⟩ b1
  exact hOver Γ (Λ.subgroupOf Γ) f2 b2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOverOfSumBoundCoindRetract

section

@[expose] public section

open CategoryTheory in
theorem UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.BA.CoindRetract → UpperTheory.V.Af.BA.BddOver := by
  intro hSum hRet
  unfold UpperTheory.V.Af.BA.BddOver
  intro G _ S hS hB
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, fun A => ?_⟩
  obtain ⟨π, ι, hπι⟩ := hRet G S hS A
  have hq : ∀ q, Module.rank ℂ ↑(groupCohomology A q) ≤
      Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q) := by
    intro q
    have h1 := hSum G Unit A (fun _ => Rep.coind S.subtype (Rep.res S.subtype A))
      (fun _ => π) (fun _ => ι) (by rw [Fintype.sum_unique]; exact hπι) q
    rw [Fintype.sum_unique,
      ((groupCohomology.coindIso (Rep.res S.subtype A) q).toLinearEquiv).rank_eq] at h1
    exact h1
  calc UpperTheory.V.Af.CohB.totCoh A
      = Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology A q)) := rfl
    _ ≤ Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q)) :=
      Cardinal.sum_le_sum _ _ hq
    _ = UpperTheory.V.Af.CohB.totCoh (Rep.res S.subtype A) := rfl
    _ ≤ c * Module.rank ℂ ↑(Rep.res S.subtype A) := hc _
    _ = c * Module.rank ℂ ↑A := rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyRankEqHomologyRank

section

@[expose] public section

open CategoryTheory

theorem UpperTheory.cohomology_rank_eq_homology_rank :
    UpperTheory.V.Af.CohB.RankHomology := by
  intro C q
  have h1 : Function.Surjective (C.homologyπ q).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have h2 : Function.Injective (C.iCycles q).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact (LinearMap.rank_le_of_surjective _ h1).trans (LinearMap.rank_le_of_injective _ h2)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCMIntegralOfExistsCM

section

@[expose] public section

open NumberField in
theorem UpperTheory.exists_CM_integral_of_exists_CM :
    UpperTheory.V.Af.BA.ExCM → UpperTheory.V.Af.BA.ExCMInt := by
  intro h F _ _ _
  obtain ⟨L, i1, i2, i3, i, s, hs, hfix⟩ := h F
  refine ⟨L, i1, i2, i3, RingOfIntegers.mapRingHom i, RingOfIntegers.mapRingHom s, ?_, ?_, ?_⟩
  · intro w x
    exact hs w.embedding (x : L)
  · intro x y hxy
    have h1 : i (x : F) = i (y : F) := congrArg (fun z : 𝓞 L => (z : L)) hxy
    exact RingOfIntegers.ext (i.injective h1)
  · intro x
    constructor
    · intro hx
      have h1 : s (x : L) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hx
      obtain ⟨y, hy⟩ := (hfix _).1 h1
      have hi : IsIntegral ℤ y := by
        have h2 : IsIntegral ℤ (i.toIntAlgHom y) := by
          have : i.toIntAlgHom y = (x : L) := hy
          rw [this]
          exact x.isIntegral_coe
        exact (isIntegral_algHom_iff i.toIntAlgHom i.injective).1 h2
      exact ⟨⟨y, hi⟩, RingOfIntegers.ext hy⟩
    · rintro ⟨y, hy⟩
      have h1 : i (y : F) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hy
      exact RingOfIntegers.ext ((hfix _).2 ⟨_, h1⟩)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PinsOfClosedSubgroupPadicCharacterInv

section

@[expose] public section

open CategoryTheory

theorem UpperTheory.pins_of_closed_subgroup_padic_character_inv :
    UpperTheory.V.Af.BA.LiftEquiv :=
  _root_.UpperTheory.Reformulated.B.Qe19.pins_of_closed_subgroup_padic_character_inv
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ProjPermOfLiftEquiv

section

@[expose] public section

open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.projPerm_of_liftEquiv :
    UpperTheory.V.Af.BA.LiftEquiv → UpperTheory.V.Af.BA.ProjPerm := by
  intro h Γ X _ _ hfin
  refine CategoryTheory.Projective.mk ?_
  intro E Y f e he
  have hs := (Rep.epi_iff_surjective e).1 he
  have heq : ∀ (g : Γ) (x : X), (Rep.Hom.hom f) (Finsupp.single (g • x) 1) =
      (Y.ρ g) ((Rep.Hom.hom f) (Finsupp.single x 1)) := by
    intro g x
    have hc := LinearMap.congr_fun ((Rep.Hom.hom f).isIntertwining' g) (Finsupp.single x 1)
    simpa [UpperTheory.V.Af.BA.permC_single] using hc
  obtain ⟨ψ, hψ, hψe⟩ := h Γ X hfin E Y e hs (fun x => (Rep.Hom.hom f) (Finsupp.single x 1)) heq
  refine ⟨Rep.ofHom (ρ := UpperTheory.V.Af.BA.permC Γ X) (σ := E.ρ)
    ⟨Finsupp.linearCombination ℂ ψ, ?_⟩, ?_⟩
  · intro g
    apply Finsupp.lhom_ext
    intro x c
    simp [UpperTheory.V.Af.BA.permC_single, hψ]
  · apply UpperTheory.V.Af.BA.PC_ext
    intro x
    simp [Rep.hom_comp, Rep.hom_ofHom, hψe]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RankCohHomOfRankHomology

section

@[expose] public section

open CategoryTheory in
theorem UpperTheory.rankCohHom_of_rankHomology :
    UpperTheory.V.Af.CohB.RankHomology → UpperTheory.V.Af.BA.RankCohHom := by
  intro hR Γ _ P q X hX A
  obtain ⟨i⟩ := hX
  rw [(groupCohomologyIsoExt A q ≪≫ P.isoExt q A).toLinearEquiv.rank_eq]
  refine (hR _ q).trans ?_
  rw [ChainComplex.linearYonedaObj_X]
  exact (Linear.homCongr ℂ i (Iso.refl A)).rank_eq.le
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealSpanOfGoodRealForm

section

@[expose] public section

open UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.real_span_of_good_real_form :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.SpanRe := by
  intro hRP hRI hG L _ _ _ N σ hσ p t ht
  apply spanpsd
  intro k hk hzero
  obtain ⟨k', hk'q, hk'P⟩ := hRP L N σ hσ k
  obtain ⟨hk'psd, hk'0⟩ := hk'P hk
  apply hk'0
  refine ConeExtensionAcyclic.simp_span (hG L N σ hσ).locFin p t ht k' hk'psd ?_
  intro y hy
  have hM : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (y : Lat L N) = 1 := by
    intro j
    have := hy j
    rw [qr_apply] at this
    exact this
  have hinvq : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (sLat σ (y : Lat L N)) = 1 := by
    intro j
    rw [((hRI L N σ hσ).2 _ (t j).1.2).1 (y : Lat L N)]
    exact hM j
  rw [qr_apply, hk'q, hzero _ hM, hzero _ hinvq]
  norm_num
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.BddArith

section

@[expose] public section

open NumberField

open CategoryTheory UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_cx : BddCx := by
  intro Γ I _ _ K hx ho hs
  obtain ⟨hst, D, hD⟩ := UpperTheory.adelic_rep_dimension_bounded Γ I K (ho 1) hs
  obtain ⟨h0, h1, h2⟩ := UpperTheory.exactCOf_of_exactBase UpperTheory.exactBase_integral_to_complex Γ I K hx
  obtain ⟨P, hP, he⟩ := UpperTheory.repResolution_exists Γ (fun p => PC Γ (K.Tup p)) K.d (augC Γ (K.Tup 0))
    (fun p => UpperTheory.projPerm_of_liftEquiv UpperTheory.pins_of_closed_subgroup_padic_character_inv Γ _ (hst p)) h0 h1 h2
  obtain ⟨a0, aD⟩ := UpperTheory.rep_hom_alternating_sum_eq_zero Γ I K
  obtain ⟨e, he1, he2⟩ := he K.alt (by rw [a0, Category.id_comp]) (UpperTheory.altChain_of_permSplit UpperTheory.perm_split_fin_succ Γ I K)
  refine UpperTheory.adelic_rep_bounded_of_degree_bounded Γ (fun q => ?_) ⟨D, fun q hq A => UpperTheory.ext_vanishing_of_resolution_endo Γ P e he1 q (he2 q (aD q (hD q hq))) A⟩
  obtain ⟨c, hc⟩ := UpperTheory.permutation_module_homology_rank Γ _ (ho q)
  exact ⟨c, fun A => (UpperTheory.rankCohHom_of_rankHomology UpperTheory.cohomology_rank_eq_homology_rank Γ P q _ (hP q) A).trans (hc A)⟩

open UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_fix : BddFix :=
  have hg : GoodRe := UpperTheory.good_real_form_of_real_part_of_real_involution UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant
  have ha : ActRe := UpperTheory.real_structure_action_of_real_involution UpperTheory.adelic_realPart_invariant
  have hs : SpanRe := UpperTheory.real_span_of_good_real_form UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant hg
  UpperTheory.bddFix_of_bounded_complex UpperTheory.V.Af.bddArith_cx hg ha hs
    (UpperTheory.orbRe_of_minimal_vector_stabilizer UpperTheory.fixedOrbits_finite_representatives UpperTheory.adelic_realPart_invariant ha hs UpperTheory.minimal_orbit_representatives UpperTheory.minimal_vector_stabilizer_property) UpperTheory.minimal_vector_stabilizer_property

theorem UpperTheory.V.Af.bddArith :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)), Subgroup.Commensurable Γ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)).range → UpperTheory.V.Af.CohB.Bdd ↥Γ := by
  intro F _ _ hF n Γ hΓ
  have hO : UpperTheory.V.Af.CohB.Bdd (GL (Fin n) (𝓞 F)) := by
    rcases hF with hF | hF
    · exact UpperTheory.bounded_complex_of_bounded_simplicial_complex UpperTheory.V.Af.bddArith_cx F n
    · obtain ⟨L, _, _, _, i, σ, hσ, hi, hf⟩ := UpperTheory.exists_CM_integral_of_exists_CM UpperTheory.exists_CM_extension F
      exact UpperTheory.cohomology_bounded_equiv _ _ (UpperTheory.building_fixed_points_equiv _ _ i σ n hi hf) (UpperTheory.V.Af.bddArith_fix L n σ hσ)
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)) := by
    intro g k e
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact RingOfIntegers.coe_injective (congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F) a b) e)
  exact UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv UpperTheory.cohomology_bounded_equiv UpperTheory.adelic_rep_bounded_of_subgroup_bounded (UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract UpperTheory.cohomology_sum_bound UpperTheory.coind_retract_of_finite_index) _ Γ _ hΓ
    (UpperTheory.cohomology_bounded_equiv _ _ ⟨MonoidHom.ofInjective hinj⟩ hO)
end
end
