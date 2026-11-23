module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.PNBasicPf
public import Development.EtaleCohomology.EtaleTrace.GenInPf
public import Development.EtaleCohomology.EtaleTrace.GenOutGluePf
public import Development.EtaleCohomology.EtaleTrace.GenUsePf
public import Development.EtaleCohomology.EtaleTrace.ChartGenOnPfCut
public import Development.EtaleCohomology.EtaleTrace.GenEtalePfCut
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
public import Development.EtaleCohomology.EtaleTrace.ChartOverKPf
public import Development.EtaleCohomology.EtaleTrace.FibrePf
import Mathlib.Tactic.Lemma
public import Development.EtaleCohomology.EtaleTrace.FieldDimPf
public import Development.EtaleCohomology.EtaleTrace.FinSurjPfAll
public import Development.EtaleCohomology.EtaleTrace.GenAwayEvalPf
public import Development.EtaleCohomology.EtaleTrace.GenEtaleAtBotPf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.EtaleCohomology.EtaleTrace.GenOfAwayPf
public import Development.EtaleCohomology.EtaleTrace.GenOnAgreePf
public import Development.EtaleCohomology.EtaleTrace.GenUseBackPf
public import Development.EtaleCohomology.EtaleTrace.HomRelPf
public import Development.EtaleCohomology.EtaleTrace.JetIndepPf
public import Development.EtaleCohomology.EtaleTrace.JetSpanPf
public import Development.EtaleCohomology.EtaleTrace.LCoverCut
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.EtaleCohomology.EtaleTrace.PNIntegralPf
public import Development.EtaleCohomology.EtaleTrace.ProjectPf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.EtaleCohomology.EtaleTrace.StepPf
public import Development.EtaleCohomology.EtaleTrace.TrdegLePf
public import Development.EtaleCohomology.KummerExtensions.EtaleProjectiveChartGenericValuationIdentity

-- Source module: Development.EtaleCohomology.EtaleTrace.ChartGenOnPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

theorem ChartGenOn_of_val (h : ChartGenVal) : ChartGenOn := ChartGenOn_of ChartGenMem_pf h

end LateralTheory.EtaleTrace.Cov
end
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.FibreOfEtalePf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

lemma isPullback_equalizer {k : Type} [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P)
    (hπ : π ≫ r = p) (t : Pt r) :
    IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π t.1 := by
  have key : ∀ {T : Scheme.{0}} (a : T ⟶ X) (b : T ⟶ S k), a ≫ π = b ≫ t.1 → a ≫ p = b := by
    intro T a b h
    rw [← hπ, ← Category.assoc, h, Category.assoc, t.2, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)
  · rw [Category.assoc]; exact equalizer.condition _ _
  · intro s
    exact equalizer.lift s.fst (by rw [s.condition, ← Category.assoc, key s.fst s.snd s.condition])
  · intro s; exact equalizer.lift_ι _ _
  · intro s
    rw [← Category.assoc, equalizer.lift_ι]; exact key s.fst s.snd s.condition
  · intro s m h1 _
    apply equalizer.hom_ext
    exact h1.trans (equalizer.lift_ι _ _).symm

theorem FibreOfEtale_of : FibreOfEtale := by
  intro k _ X P p r π hπ V hE t ht
  have hr : Set.range t.1.base ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact ht x
  set t' := IsOpenImmersion.lift V.ι t.1 hr
  have ht' : t' ≫ V.ι = t.1 := IsOpenImmersion.lift_fac _ _ _
  have s := (congrArg (IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π) ht').mpr
    (isPullback_equalizer p r π hπ t)
  have h := IsPullback.of_right' s (isPullback_morphismRestrict π V).flip
  exact MorphismProperty.of_isPullback h hE

end LateralTheory.EtaleTrace.Cov
end
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.GenEtalePfData

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem genAffineData : GenAffineData := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj
  obtain ⟨x⟩ : Nonempty P := inferInstance
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens (show x ∈ (⊤ : P.Opens) from trivial)
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  refine ⟨U, hU, ⟨x, hxU⟩, hU', ?_, ?_, ?_⟩
  · have hft : (r.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) r hr ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    letI := (r.appLE ⊤ U le_top).hom.toAlgebra
    haveI : IsNoetherianRing Γ(S k, ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
    haveI : Algebra.FiniteType Γ(S k, ⊤) Γ(P, U) := hft
    exact Algebra.FiniteType.isNoetherianRing Γ(S k, ⊤) Γ(P, U)
  · haveI : IsAffine U := hU
    have h0 : (π ∣_ U).appTop.hom.Finite := (π ∣_ U).finite_appTop
    rw [morphismRestrict_appTop] at h0
    have gen : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = U →
        RingHom.Finite (π.app W ≫ X.presheaf.map (eqToHom h).op).hom → RingHom.Finite (π.app U).hom := by
      rintro W T h rfl
      subst h
      simp
    exact gen _ _ _ (by simp) h0
  · haveI : IsDominant π := inferInstance
    haveI : IsSchemeTheoreticallyDominant π := .of_isDominant π
    exact π.app_injective U

theorem GenEtale_of_atBot (h : GenEtaleAtBot) : GenEtale := GenEtale_of' genAffineData h

end LateralTheory.EtaleTrace.Cov
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.JetUnramPf

section

@[expose] public section

namespace LateralTheory.EtaleTrace.Cov

open KaehlerDifferential in
theorem JetUnram_of : JetUnram := by
  intro k K O _ _ _ _ φ n w i hwi hspan hk hw
  let _ : Algebra O K := φ.toAlgebra
  show Algebra.FormallyUnramified O K
  constructor
  have hD0 : ∀ z ∈ φ.range, D O K z = 0 := by
    rintro _ ⟨o, rfl⟩
    exact (D O K).map_algebraMap o
  let D' : Derivation k K Ω[K⁄O] := Derivation.mk'
    { toFun := fun x => D O K x
      map_add' := fun x y => (D O K).map_add x y
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, (D O K).leibniz, hD0 _ (hk c), smul_zero, add_zero, algebraMap_smul] }
    (fun a b => (D O K).leibniz a b)
  have hD' : ∀ x, D'.liftKaehlerDifferential (D k K x) = D O K x := fun x =>
    D'.liftKaehlerDifferential_comp_D x
  let G : (K × Ω[K⁄k]) →ₗ[K] Ω[K⁄O] :=
    D'.liftKaehlerDifferential.comp (LinearMap.snd K K Ω[K⁄k]) -
      (LinearMap.fst K K Ω[K⁄k]).smulRight ((w i)⁻¹ • D O K (w i))
  have hG : ∀ j, G (jet k w j) = 0 := by
    intro j
    obtain ⟨u, hu⟩ := hw j
    have hwj : w j = φ u * w i := by rw [hu]; field_simp
    show D'.liftKaehlerDifferential (D k K (w j)) - w j • ((w i)⁻¹ • D O K (w i)) = 0
    rw [hD', hwj, (D O K).leibniz, hD0 _ ⟨u, rfl⟩, smul_zero, add_zero, smul_smul, mul_assoc,
      mul_inv_cancel₀ hwi, mul_one, sub_self]
  have hG0 : G = 0 := LinearMap.ext_on_range hspan (fun j => by rw [hG j]; rfl)
  have hDz : ∀ x : K, D O K x = 0 := by
    intro x
    have h := LinearMap.congr_fun hG0 (0, D k K x)
    have h2 : G (0, D k K x) = D O K x := by
      show D'.liftKaehlerDifferential (D k K x) - (0 : K) • ((w i)⁻¹ • D O K (w i)) = D O K x
      rw [hD', zero_smul, sub_zero]
    rw [← h2, h]; rfl
  suffices (⊤ : Submodule K Ω[K⁄O]) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun y => this trivial
  rw [← span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hDz x

end LateralTheory.EtaleTrace.Cov
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.RatPtInPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem RatPtIn_of : RatPtIn := by
  intro k _ _ P r hr V hV
  have := hr
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace r
  obtain ⟨x, hxV, hxc⟩ := nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed
  refine ⟨⟨pointOfClosedPoint r x hxc, pointOfClosedPoint_comp r x hxc⟩, fun a => ?_⟩
  have h := pointOfClosedPoint_apply r x hxc a
  show (pointOfClosedPoint r x hxc) a ∈ V
  rw [h]; exact hxV

end LateralTheory.EtaleTrace.Cov
end
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.FinLCover

section

@[expose] public section

namespace LateralTheory.Fin.LCover
theorem projective_space_over_field_integral : LateralTheory.EtaleTrace.Cov.PNIntegral := by
  apply LateralTheory.EtaleTrace.Cov.PNIntegral_of
theorem projective_space_standard_chart_basic_properties : LateralTheory.EtaleTrace.Cov.PNBasic := by
  apply LateralTheory.EtaleTrace.Cov.PNBasic_of <;> first | exact projective_space_over_field_integral
theorem homogeneous_localization_away_generator_evaluation : LateralTheory.EtaleTrace.Cov.GenInPf.GenAwayEval := by
  apply LateralTheory.EtaleTrace.Cov.GenInPf.GenAwayEval_of
theorem homogeneous_localization_away_generated_by_coordinates : LateralTheory.EtaleTrace.Cov.GenInPf.GenOfAway := by
  apply LateralTheory.EtaleTrace.Cov.GenInPf.GenOfAway_of
theorem projective_coordinates_generate_inside_chart : LateralTheory.EtaleTrace.Cov.GenIn := by
  apply LateralTheory.EtaleTrace.Cov.GenIn_of <;> first | exact homogeneous_localization_away_generator_evaluation | exact homogeneous_localization_away_generated_by_coordinates
theorem projective_chart_ring_hom_over_field : LateralTheory.EtaleTrace.Cov.ChartOverK := by
  apply LateralTheory.EtaleTrace.Cov.ChartOverK_of
theorem projective_chart_generic_section_values_agree : LateralTheory.EtaleTrace.Cov.ChartGenVal := by
  apply SchemeAppLEComposition.Cb.etale_projective_chart_generic_valuation_identity
theorem projective_chart_generic_section_on_open : LateralTheory.EtaleTrace.Cov.ChartGenOn := by
  apply LateralTheory.EtaleTrace.Cov.ChartGenOn_of_val <;> first | exact projective_chart_generic_section_values_agree
theorem projective_coordinate_sections_generate_on_chart : LateralTheory.EtaleTrace.Cov.GenOutChart := by
  apply LateralTheory.EtaleTrace.Cov.GenOutChart_of_two <;> first | exact projective_chart_ring_hom_over_field | exact projective_chart_generic_section_on_open
theorem projective_coordinate_sections_agree_on_overlap : LateralTheory.EtaleTrace.Cov.GenOnAgree := by
  apply LateralTheory.EtaleTrace.Cov.GenOnAgree_of
theorem projective_coordinate_sections_glue_across_charts : LateralTheory.EtaleTrace.Cov.GenOutGlue := by
  apply LateralTheory.EtaleTrace.Cov.GenOutGlue_of_agree <;> first | exact projective_coordinate_sections_agree_on_overlap
theorem projective_coordinate_sections_generate_outside_hyperplane : LateralTheory.EtaleTrace.Cov.GenOut := by
  apply LateralTheory.EtaleTrace.Cov.GenOut_of <;> first | exact projective_coordinate_sections_generate_on_chart | exact projective_coordinate_sections_glue_across_charts
theorem function_field_generators_pull_back_to_chart : LateralTheory.EtaleTrace.Cov.GenUseBack := by
  apply LateralTheory.EtaleTrace.Cov.GenUseBack_of
theorem projective_coordinates_generate_function_field : LateralTheory.EtaleTrace.Cov.GenUse := by
  apply LateralTheory.EtaleTrace.Cov.GenUse_of <;> first | exact function_field_generators_pull_back_to_chart
theorem coordinate_differentials_span_function_field_kaehler : LateralTheory.EtaleTrace.Cov.JetSpan := by
  apply LateralTheory.EtaleTrace.Cov.JetSpan_of
theorem function_field_transcendence_degree_le_dim : LateralTheory.EtaleTrace.Cov.TrdegLe := by
  apply LateralTheory.EtaleTrace.Cov.TrdegLe_of
theorem homogeneous_relation_coordinate_integral_dependence : LateralTheory.EtaleTrace.Cov.HomRel := by
  apply LateralTheory.EtaleTrace.Cov.HomRel_of
theorem linear_projection_reduce_ambient_dimension : LateralTheory.EtaleTrace.Cov.Step := by
  apply LateralTheory.EtaleTrace.StepPf.Step_of
theorem linear_projection_etale_cover_exists : LateralTheory.EtaleTrace.Cov.Project := by
  apply LateralTheory.EtaleTrace.Cov.Project_of <;> first | exact linear_projection_reduce_ambient_dimension | exact homogeneous_relation_coordinate_integral_dependence
theorem generic_linear_forms_independent_differentials : LateralTheory.EtaleTrace.Cov.JetIndep := by
  apply LateralTheory.EtaleTrace.Cov.JetIndep_of
theorem linear_projection_unramified_of_independent_differentials : LateralTheory.EtaleTrace.Cov.JetUnram := by
  apply LateralTheory.EtaleTrace.Cov.JetUnram_of
theorem kaehler_differentials_function_field_rank_eq_dim : LateralTheory.EtaleTrace.Cov.FieldDim := by
  apply LateralTheory.EtaleTrace.Cov.FieldDim_of
theorem linear_projection_finite_surjective_onto_affine_space : LateralTheory.EtaleTrace.Cov.FinSurj := by
  apply LateralTheory.EtaleTrace.Cov.FinSurj_of_full <;> first | exact projective_space_standard_chart_basic_properties
theorem finite_cover_etale_at_generic_point : LateralTheory.EtaleTrace.Cov.GenEtaleAtBot := by
  apply LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf.GenEtaleAtBot_of
theorem finite_surjective_unramified_generically_etale : LateralTheory.EtaleTrace.Cov.GenEtale := by
  apply LateralTheory.EtaleTrace.Cov.GenEtale_of_atBot <;> first | exact finite_cover_etale_at_generic_point
theorem rational_point_in_nonempty_open_over_alg_closed : LateralTheory.EtaleTrace.Cov.RatPtIn := by
  apply LateralTheory.EtaleTrace.Cov.RatPtIn_of
theorem etale_fibre_over_rational_point_of_etale_restriction : LateralTheory.EtaleTrace.Cov.FibreOfEtale := by
  apply LateralTheory.EtaleTrace.Cov.FibreOfEtale_of
theorem finite_cover_etale_fibre_over_rational_point : LateralTheory.EtaleTrace.Cov.Fibre := by
  apply LateralTheory.EtaleTrace.Cov.Fibre_of <;> first | exact finite_surjective_unramified_generically_etale | exact rational_point_in_nonempty_open_over_alg_closed | exact etale_fibre_over_rational_point_of_etale_restriction
theorem etale_finite_cover_of_smooth_variety : LateralTheory.EtaleTrace.LCover := by
  apply LateralTheory.EtaleTrace.Cov.goal_of <;> first | exact projective_space_standard_chart_basic_properties | exact projective_coordinates_generate_inside_chart | exact projective_coordinate_sections_generate_outside_hyperplane | exact projective_coordinates_generate_function_field | exact coordinate_differentials_span_function_field_kaehler | exact function_field_transcendence_degree_le_dim | exact homogeneous_relation_coordinate_integral_dependence | exact linear_projection_reduce_ambient_dimension | exact linear_projection_etale_cover_exists | exact generic_linear_forms_independent_differentials | exact linear_projection_unramified_of_independent_differentials | exact kaehler_differentials_function_field_rank_eq_dim | exact linear_projection_finite_surjective_onto_affine_space | exact finite_cover_etale_fibre_over_rational_point
theorem intersectionNumber_baseChange : LateralTheory.EtaleTrace.LCover := etale_finite_cover_of_smooth_variety
end LateralTheory.Fin.LCover
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinCov

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.finCov_holds :
    UpperTheory.Gal.KunnethLefschetz.FinCov := by
  unfold UpperTheory.Gal.KunnethLefschetz.FinCov
  intro k _ _ d X p h1 h2 h3
  obtain ⟨π, t, e1, e2, e3, -⟩ := LateralTheory.Fin.LCover.intersectionNumber_baseChange k d p h1 h2 h3
  exact ⟨π, e1, e2, e3⟩
end
end
end
