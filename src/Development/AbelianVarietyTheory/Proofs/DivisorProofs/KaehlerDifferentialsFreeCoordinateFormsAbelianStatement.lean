module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformisedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePiLiftKaehlerCoordinateDerivationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutingCoordinateDerivationsRegularFunct

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_commuting_derivations_of_values {R : Type} [CommRing R] [Algebra ℂ R] {g : ℕ} (P : Set (Fin g → ℂ))
    (v : R → (Fin g → ℂ) → ℂ) (hP : IsOpen P) (hd : ∀ x, DifferentiableOn ℂ (v x) P)
    (he : ∀ z ∈ P, ∃ e : R →ₐ[ℂ] ℂ, ∀ b, v b z = e b) (hinj : ∀ x, (∀ z ∈ P, v x z = 0) → x = 0)
    (hder : ∀ x w, ∃ y, ∀ z ∈ P, fderiv ℂ (v x) z w = v y z) :
    ∃ d : Fin g → Derivation ℂ R R, (∀ a b x, d a (d b x) = d b (d a x)) ∧
      ∀ a x, ∀ z ∈ P, v (d a x) z = fderiv ℂ (v x) z (Pi.single a 1) := by
  choose D hD using hder
  have hext : ∀ x y, (∀ z ∈ P, v x z = v y z) → x = y := fun x y h ↦ by
    refine sub_eq_zero.1 (hinj _ fun z hz ↦ ?_)
    obtain ⟨e, he⟩ := he z hz
    rw [he, map_sub, ← he, ← he, h z hz, sub_self]
  have hadd : ∀ x y, ∀ z ∈ P, v (x + y) z = v x z + v y z := fun x y z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_add (f := _)]
  have hmul : ∀ x y, ∀ z ∈ P, v (x * y) z = v x z * v y z := fun x y z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_mul]
  have hsmul : ∀ (c : ℂ) x, ∀ z ∈ P, v (c • x) z = c • v x z := fun c x z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_smul]
  have hat : ∀ x, ∀ z ∈ P, DifferentiableAt ℂ (v x) z := fun x z hz ↦ (hd x).differentiableAt (hP.mem_nhds hz)
  have hcongr : ∀ (f k : (Fin g → ℂ) → ℂ), (∀ z ∈ P, f z = k z) → ∀ z ∈ P, fderiv ℂ f z = fderiv ℂ k z :=
    fun f k h z hz ↦ Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hP.mem_nhds hz) h)
  let Dl : (Fin g → ℂ) → R →ₗ[ℂ] R := fun w ↦
    { toFun := fun x ↦ D x w
      map_add' := fun x y ↦ hext _ _ fun z hz ↦ by
        rw [hadd _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
          hcongr _ (v x + v y) (hadd x y) z hz, fderiv_add (hat x z hz) (hat y z hz)]
        rfl
      map_smul' := fun c x ↦ hext _ _ fun z hz ↦ by
        rw [RingHom.id_apply, hsmul _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
          hcongr _ (c • v x) (hsmul c x) z hz, fderiv_const_smul (hat x z hz)]
        rfl }
  have hL : ∀ w x y, Dl w (x * y) = x • Dl w y + y • Dl w x := fun w x y ↦ hext _ _ fun z hz ↦ by
    change v (D (x * y) w) z = v (x * D y w + y * D x w) z
    rw [hadd _ _ z hz, hmul _ _ z hz, hmul _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
      hcongr _ (v x * v y) (hmul x y) z hz, fderiv_mul (hat x z hz) (hat y z hz)]
    rfl
  have h2 : ∀ x w w', ∀ z ∈ P, v (D (D x w) w') z = fderiv ℂ (fderiv ℂ (v x)) z w' w := fun x w w' z hz ↦ by
    have ha : AnalyticAt ℂ (v x) z := ReciprocityTheory.AnForm.Osgood.osgood g P (v x) hP (hd x) z hz
    rw [← hD _ _ z hz, ← hcongr _ _ (hD x w) z hz,
      fderiv_clm_apply ha.fderiv.differentiableAt (differentiableAt_const w)]
    simp
  refine ⟨fun a ↦ Derivation.mk' (Dl (Pi.single a 1)) (hL _), fun a b x ↦ hext _ _ fun z hz ↦ ?_,
    fun a x z hz ↦ (hD x _ z hz).symm⟩
  have ha : AnalyticAt ℂ (v x) z := ReciprocityTheory.AnForm.Osgood.osgood g P (v x) hP (hd x) z hz
  change v (D (D x _) _) z = v (D (D x _) _) z
  rw [h2 _ _ _ z hz, h2 _ _ _ z hz]
  exact (ha.contDiffAt (n := ⊤)).isSymmSndFDerivAt le_top _ _

theorem exists_commuting_coordinate_derivations : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), ∃ d : Fin g → Derivation ℂ (Sec (str A) U) (Sec (str A) U), (∀ a b x, d a (d b x) = d b (d a x)) ∧ ∀ a x, ∀ z ∈ pre u.ex U, val u.ex U (d a x) z = fderiv ℂ (val u.ex U x) z (Pi.single a 1) := by
  intro A _ g L u hA U
  obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  exact exists_commuting_derivations_of_values (R := Sec (str A) U) (pre u.ex U) (val u.ex U) (h1 U) (h2 U) (h10 U)
    (GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U) (GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised A g L u hA U)

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutingCoordinateDerivationsRegularFunctStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_commuting_coordinate_derivations_regular_functions : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), ∃ d : Fin g → Derivation ℂ (Sec (str A) U) (Sec (str A) U), (∀ a b x, d a (d b x) = d b (d a x)) ∧ ∀ a x, ∀ z ∈ pre u.ex U, val u.ex U (d a x) z = fderiv ℂ (val u.ex U x) z (Pi.single a 1) := by
  first | exact @GlobalTheory.CechPer.exists_commuting_coordinate_derivations | exact GlobalTheory.CechPer.exists_commuting_coordinate_derivations | (intros; apply GlobalTheory.CechPer.exists_commuting_coordinate_derivations <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfSurjectiveProjectiveConstRank

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem injective_of_surjective_of_rankAtStalk_eq : ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (g : ℕ) (f : M →ₗ[B] (Fin g → B)), Module.Finite B M → Module.Projective B M → (∀ p : PrimeSpectrum B, Module.rankAtStalk M p = g) → Function.Surjective f → Function.Injective f := by
  intro B M _ _ _ g f hf hp hr hs
  refine (Module.bijective_of_surjective_of_rankAtStalk_eq hs ?_).1
  intro m hm
  have : Nontrivial B := ⟨⟨0, 1, fun h => hm.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact m.zero_mem)⟩⟩
  rw [hr, Module.rankAtStalk_eq_finrank_of_free]
  simp

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfSurjectiveProjectiveConstRankStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.injective_of_surjective_projective_constRank : ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (g : ℕ) (f : M →ₗ[B] (Fin g → B)), Module.Finite B M → Module.Projective B M → (∀ p : PrimeSpectrum B, Module.rankAtStalk M p = g) → Function.Surjective f → Function.Injective f := by
  first | exact @GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq | exact GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq | (intros; apply GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerAffineOpenFiniteProjectiveRank

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem locally_standardSmooth_sec (A : Over (Sp ℂ)) (g : ℕ) (h : SmoothOfRelativeDimension g A.hom) (U : A.left.affineOpens) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap ℂ (Sec (str A) U.1)) := by
  have h' : SmoothOfRelativeDimension g (str A) := by
    simpa [str] using h
  have h1 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) (str A) h' ⟨⊤, isAffineOpen_top _⟩ U le_top
  have hr := RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := g))
  exact hr.2 _ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv h1

theorem kaehler_sec_finite_projective_rank : ∀ (A : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ U : A.left.affineOpens, Module.Finite (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ Module.Projective (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ ∀ p : PrimeSpectrum (Sec (str A) U.1), Module.rankAtStalk Ω[Sec (str A) U.1⁄ℂ] p = g := by
  intro A g h U
  have hl := locally_standardSmooth_sec A g h U
  haveI := GlobalTheory.AugCot.smooth_of_locally hl
  exact ⟨inferInstance, inferInstance, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally hl⟩

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerAffineOpenFiniteProjectiveRankStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kaehler_affineOpen_finite_projective_rank : ∀ (A : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ U : A.left.affineOpens, Module.Finite (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ Module.Projective (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ ∀ p : PrimeSpectrum (Sec (str A) U.1), Module.rankAtStalk Ω[Sec (str A) U.1⁄ℂ] p = g := by
  first | exact @GlobalTheory.CechPer.kaehler_sec_finite_projective_rank | exact GlobalTheory.CechPer.kaehler_sec_finite_projective_rank | (intros; apply GlobalTheory.CechPer.kaehler_sec_finite_projective_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerDifferentialsFreeCoordinateFormsAbelian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem kaehler_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens), ∃ (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)) (ω : Fin g → Ω[Sec (str A) U.1⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) ∧ (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) ∧ (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) ∧ (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) ∧ ∀ a ξ, ∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ (Pi.single a 1) = val u.ex U.1 ((d a).liftKaehlerDifferential ξ) z := by
  intro A _ g L u hA U
  obtain ⟨d, hcomm, hval⟩ := GlobalTheory.T.exists_commuting_coordinate_derivations_regular_functions A g L u hA U.1
  have hsm := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.kaehler_affineOpen_finite_projective_rank A g hsm U
  have hsurj := GlobalTheory.T.surjective_pi_liftKaehler_coordinateDerivations A g L u hA U d hval
  set Φ : Ω[Sec (str A) U.1⁄ℂ] →ₗ[Sec (str A) U.1] (Fin g → Sec (str A) U.1) :=
    LinearMap.pi fun a => (d a).liftKaehlerDifferential with hΦ
  have hinj : Function.Injective Φ := GlobalTheory.T.injective_of_surjective_projective_constRank _ _ g Φ hfin hproj hrk hsurj
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦa : ∀ ξ a, Φ ξ a = (d a).liftKaehlerDifferential ξ := fun ξ a => rfl
  refine ⟨d, fun b => e.symm (Pi.single b 1), hcomm, hval, ?_, ?_, ?_⟩
  · intro a b
    rw [← hΦa]
    have : Φ (e.symm (Pi.single b 1)) = Pi.single b 1 := e.apply_symm_apply _
    rw [this, Pi.single_apply]
  · intro ξ
    apply hinj
    funext c

    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply]
    have h1 : ∀ b, Φ (e.symm (Pi.single b 1)) = Pi.single b 1 := fun b => e.apply_symm_apply _
    simp only [h1]
    rw [Finset.sum_eq_single c (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero])
      (fun h => absurd (Finset.mem_univ c) h), Pi.single_eq_same, hΦa]
    exact (_root_.mul_one _).symm
  · intro a ξ z hz
    obtain ⟨ev, hev⟩ := (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz
    obtain ⟨_, hsm', hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz
    have hmem : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    have hev' : ∀ b : Sec (str A) U.1, val u.ex U.1 b z = ev b := hev
    suffices h : evForm u.ex U.1 z ξ (Pi.single a 1) = ev ((d a).liftKaehlerDifferential ξ) from
      h.trans (hev' _).symm
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [hD, Derivation.liftKaehlerDifferential_comp_D]
      exact (hval a y z hz).symm.trans (hev' _)
    | zero => simp only [map_zero, ContinuousLinearMap.zero_apply]
    | add x y _ _ hx hy => simp only [map_add (f := _), ContinuousLinearMap.add_apply, hx, hy]
    | smul r x _ hx =>
      rw [hsm', ContinuousLinearMap.smul_apply, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul, hev' r]

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerDifferentialsFreeCoordinateFormsAbelianStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens), ∃ (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)) (ω : Fin g → Ω[Sec (str A) U.1⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) ∧ (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) ∧ (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) ∧ (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) ∧ ∀ a ξ, ∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ (Pi.single a 1) = val u.ex U.1 ((d a).liftKaehlerDifferential ξ) z := by
  first | exact @GlobalTheory.CechPer.kaehler_frame | exact GlobalTheory.CechPer.kaehler_frame | (intros; apply GlobalTheory.CechPer.kaehler_frame <;> assumption)
end
end
