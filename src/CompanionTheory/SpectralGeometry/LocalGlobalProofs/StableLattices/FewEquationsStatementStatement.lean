module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DependencyStatementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankBoundAtClosedPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsLocalIdealStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftMinimalGeneratorsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftModuloMaximalStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdeal

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem gr_pull_g {X Y Z : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : F (r z) ∈ M.U i) (hj : F (r z) ∈ M.U j)
    (hm : r z ∈ (M.pull F).U (fun _ => i) ⊓ (M.pull F).U (fun _ => j)) :
    gr r z _ hm ((M.pull F).g (fun _ => i) (fun _ => j)).val =
      gr (r ≫ F) z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val := by
  refine (congrArg (fun u => gr r z _ hm (Units.val u))
    ((Fintype.prod_unique (fun _ : PUnit => _ ^ (1 : ℤ))).trans (zpow_one _))).trans ?_
  exact gr_res r z _ hm _

theorem app_eq_zero_of_mem_ext {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    (U : X.Opens) {a : Γ(X, U)} (ha : a ∈ ext s J U) :
    ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom a = 0 := by
  have hle : ext s J U ≤
      RingHom.ker ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom := by
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker,
      app_cst (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))).w U r,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  exact hle ha

theorem triv_of_compatible_mod (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R)
    (M : LB X) (hM : M.IsLB) (A : Type) (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (hV : ⨆ a, V a = ⊤) (y z : ∀ a, Γ(X, V a))
    (hyz : ∀ a, y a * z a - 1 ∈ ext s J (V a))
    (hc : ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
      ext s J (V a ⊓ V b)) :
    GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  set π := pullback.fst s (spMap (Ideal.Quotient.mk J)) with hπ
  have cov : ⨆ a, π ⁻¹ᵁ V a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]; rfl
  refine gen_of_refine (pull_isLB hM π) (fun a => π ⁻¹ᵁ V a) cov (fun a _ => j a)
    (fun a => pull_le M π (j a) (hj a)) (fun a => (π.app (V a)).hom (y a))
    (fun a => IsUnit.of_mul_eq_one ((π.app (V a)).hom (z a)) ?_) fun a b x ha hb => ?_
  · have h := app_eq_zero_of_mem_ext s J (V a) (hyz a)
    rw [map_sub, map_mul, map_one, sub_eq_zero] at h
    exact h
  · have hab : (𝟙 _ : pullback s (spMap (Ideal.Quotient.mk J)) ⟶ _) x ∈ π ⁻¹ᵁ (V a ⊓ V b) :=
      ⟨ha, hb⟩
    have h := congrArg (gr (𝟙 _) x (π ⁻¹ᵁ (V a ⊓ V b)) hab)
      (app_eq_zero_of_mem_ext s J (V a ⊓ V b) (hc a b))
    rw [map_zero, gr_app, map_sub, map_mul, tr, gr_res, gr_res, gr_res, sub_eq_zero] at h
    refine (gr_app _ _ _ _ _ _).trans (h.trans ?_)
    rw [gr_app]
    exact congrArg (· * _) (gr_pull_g M π (𝟙 _) x (hj a ha) (hj b hb) _).symm

end GlobalTheory.CompanionTheory.FewEq
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdealStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.cocycle_units_trivialize_modulo_ideal : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)), ⨆ a, V a = ⊤ →
    ∀ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) →
      (∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | exact GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | (intros; apply GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankBoundAtClosedPointStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.first_cohomology_rank_bound_at_closed_point : DepSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ n r : ℕ, n < r →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ (A : Type) (V : A → X.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
      (∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d)) →
      ∃ (e : Fin r → R) (β : ∀ a, Γ(X, V a)), (∃ l, IsUnit (e l)) ∧ ∀ a c,
        ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
          ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre | exact GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre | (intros; apply GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialPullbackGivesUnitCocycle

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem exists_local_of_gen {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    {π : Y ⟶ X} {f' : Y ⟶ Sp (R ⧸ J)}
    (H : IsPullback π f' s (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a))
    (hV : ∀ a, IsAffineOpen (V a)) (hVV : ∀ a b, IsAffineOpen (V a ⊓ V b))
    (t : LB.Gen (M.pull π)) (ht : t.IsGen) :
    ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
      ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
        ext s J (V a ⊓ V b) := by
  choose y hy using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a).val)
  choose z hz using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a)⁻¹.val)
  refine ⟨y, z, fun a => ?_, fun a b => ?_⟩
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hV a) (y a * z a - 1) (by
      rw [map_sub, map_mul, map_one, hy, hz, ← map_mul, Units.mul_inv, map_one, sub_self])
    rwa [Ideal.mk_ker] at h
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hVV a b)
      (rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b)) (gr_ext fun w hw => by
        have e : ∀ c (h : (𝟙 Y ≫ π) w ∈ V c), gr (𝟙 Y ≫ π) w (V c) h (y c) =
            gr (𝟙 Y) w _ (pull_le M π (j c) le_rfl (hj c h)) (t.s fun _ => j c).val := fun c h =>
          (gr_app (𝟙 Y) π w (V c) h (y c)).symm.trans
            ((congrArg _ (hy c)).trans (gr_res (𝟙 Y) w _ h _))
        refine (gr_app _ _ _ _ _ _).trans ?_
        simp only [tr]
        rw [map_zero, map_sub, map_mul, gr_res, gr_res, gr_res, e, e, sub_eq_zero]
        exact gr_gen ht (𝟙 Y) w (hj a hw.1) (hj b hw.2))
    rwa [Ideal.mk_ker] at h

theorem exists_local_of_triv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)),
      (∀ a, IsAffineOpen (V a)) → (∀ a b, IsAffineOpen (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) →
      ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b) := by
  intro R _ X s J M _ A V j hj hV hVV ⟨t, ht⟩
  exact exists_local_of_gen s J (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))) M A V j
    hj hV hVV t ht

end GlobalTheory.CompanionTheory.FewEq
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialPullbackGivesUnitCocycleStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.trivial_pullback_gives_unit_cocycle : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)),
      (∀ a, IsAffineOpen (V a)) → (∀ a b, IsAffineOpen (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) →
      ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.exists_local_of_triv | exact GlobalTheory.CompanionTheory.FewEq.exists_local_of_triv | (intros; apply GlobalTheory.CompanionTheory.FewEq.exists_local_of_triv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem fewEq : FewEqSt := by
  have gen := GlobalTheory.T.cocycle_units_trivialize_modulo_ideal
  have data := GlobalTheory.T.trivial_pullback_gives_unit_cocycle
  have mingens := GlobalTheory.T.minimal_generators_local_ideal
  have flat := GlobalTheory.T.minimal_generators_base_change
  have dep := GlobalTheory.T.dependency_statement
  have fibre := GlobalTheory.T.first_cohomology_rank_bound_at_closed_point
  have cocycle := GlobalTheory.T.unit_cocycle_lift_modulo_maximal
  have finish := GlobalTheory.T.unit_cocycle_lift_minimal_generators
  intro R _ _ _ X s n hsm hpr hF M hM I hI hJ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  obtain ⟨r, t, ht, hmin⟩ := mingens R I
  have hsep : X.IsSeparated := by
    have : IsSeparated (s ≫ terminal.from (Sp R)) := inferInstance
    rw [Subsingleton.elim (s ≫ terminal.from (Sp R)) (terminal.from X)] at this
    exact ⟨this⟩
  haveI : Flat s := inferInstance

  let A := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : A → X.Opens := fun a => a.1.2
  let j : A → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hA : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  have hAA : ∀ a b, IsAffineOpen (V a ⊓ V b) := fun a b => (hA a).inf (hA b)
  have hAAA : ∀ a b d, IsAffineOpen (V a ⊓ V b ⊓ V d) := fun a b d => (hAA a b).inf (hA d)
  have hV : ⨆ a, V a = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  have hsq : I * I ≤ IsLocalRing.maximalIdeal R * I := Ideal.mul_mono_left hIm
  suffices hrn : r ≤ n by
    refine ⟨fun i => if h : i.1 < r then t ⟨i.1, h⟩ else 0, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i.1 < r
      · simp only [h, dif_pos]
        rw [← ht]
        exact Ideal.subset_span ⟨_, rfl⟩
      · simp only [h, dif_neg, not_false_eq_true]
        exact zero_mem _
    · rw [← ht, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.subset_span ⟨⟨i.1, i.2.trans_le hrn⟩, ?_⟩
      simp
  by_contra hrn
  obtain ⟨u, z, hz, hc⟩ := data R X s I M hM A V j hj hA hAA ((hJ I).2 le_rfl)

  let w : ∀ a, Γ(X, V a) := fun a => z a * (2 - u a * z a)
  have hw : ∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := fun a => by
    have h2 : (u a * z a - 1) * (u a * z a - 1) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := by
      refine Ideal.map_mono hsq ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (hz a) (hz a)
    have : u a * w a - 1 = -((u a * z a - 1) * (u a * z a - 1)) := by simp only [w]; ring
    rw [this]
    exact neg_mem h2
  obtain ⟨b, hb1, hb2⟩ := cocycle R X s _ I r t ht hIm M hM A V j hj u w hw hc
  have hb3 : ∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d) := fun i a c d =>
    flat R _ _ (GlobalTheory.SmallExtLift.cst_flat s (hAAA a c d)) r t I ht hmin _ (hb1 a c d) i
  obtain ⟨e, β, ⟨l, hl⟩, he⟩ := fibre dep R X s inferInstance n r (not_le.1 hrn) hF A V hV hA b hb3
  obtain ⟨J, y, z', hIJ, hy1, hy2⟩ := finish R X s I r t ht hIm hmin M A V j hj u w b e β l hw hb2 hl he
  exact hIJ ((hJ J).1 (gen R X s J M hM A V j hj hV y z' hy1 hy2))

end GlobalTheory.CompanionTheory.FewEq
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FewEquationsStatementStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

theorem _root_.GlobalTheory.T.FewEquationsStatement : FewEqSt := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.fewEq | exact GlobalTheory.CompanionTheory.FewEq.fewEq | (intros; apply GlobalTheory.CompanionTheory.FewEq.fewEq <;> assumption)
end
end
