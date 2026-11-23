module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
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
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingCompOfSaturating
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexOfNoetherianModel
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwistedSectionsCubeBijective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnFinitePresentationProjective
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModelStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CstSmoothAndFlat

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.Cohom

theorem cst_smooth_and_flat : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (V : Y.Opens), IsAffineOpen V → (Smooth f → (cst f V).Smooth) ∧ (Flat f → (cst f V).Flat) := by
  intro R _ Y f V hV
  have e : cst f V = (f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl
  have hb : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [e]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact (RingHom.Smooth.of_bijective hb).comp (f.smooth_appLE (isAffineOpen_top _) hV le_top)
  · exact (RingHom.Flat.of_bijective hb).comp (f.flat_appLE (isAffineOpen_top _) hV le_top)

end GlobalTheory.Cohom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveCechComplexLineBundle

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.Cohom

theorem exists_finite_projective_complex_cechLB : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → Smooth f → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechLB f M (fun i => nonzeroLocus (s i))), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  intro R _ Y f H m s M hH hM hs hf
  have hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V)
      fun i t => SecOnR.mulSec f M t (s i) V := fun V i j t x =>
    SecOn.mulSec_comm (s i) (s j) x
  obtain ⟨R₀, hR₀, C₀, θ, hflat, hfin, hθ⟩ :=
    exists_noetherian_model_grCube (Fin (m + 1)) R (GrSum (hx ⊤)) (GrSum.grading (hx ⊤)) fun i => by
      obtain ⟨haff, r, hr, hsurj⟩ := hs.2 i
      obtain ⟨hri, ε, hε, hker, -⟩ := GlobalTheory.AbLaw.exists_dehom_chart R Y f H m s M hH hM hs hx i r hr
      letI := cstAlgebra f (nonzeroLocus (s i))
      obtain ⟨hfp, hproj⟩ := secOn_finitePresentation_projective Y (tw M H 0) (nonzeroLocus (s i))
        (isLB_tw hM hH 0) haff
      exact ⟨Γ(Y, nonzeroLocus (s i)), inferInstance, cstAlgebra f _, MvPolynomial.aeval r,
        SecOn (tw M H 0) (nonzeroLocus (s i)), inferInstance, inferInstance, ε,
        (cst_smooth_and_flat R Y f _ haff).1 hf, hfp, hproj, hsurj,
        (MvPolynomial.aeval_X r i).trans hri, hε, hker⟩
  obtain ⟨γ, hγ⟩ := GlobalTheory.exists_grCube_twistedSections_hom_secCube_bijective R Y f H m s M hH hM hs hx 0
  let e := secCubeIso f (fun i => nonzeroLocus (s i)) (SecOn.twZeroEquiv hM hH)
    (SecOn.twZeroEquiv_restrict hM hH)
  obtain ⟨K, φ, -, hK, hφ⟩ := exists_finite_projective_complex_of_noetherian_model (Fin (m + 1)) R₀ R
    C₀ (secCube f M fun i => nonzeroLocus (s i)) (θ ≫ γ ≫ e.inv) hflat hfin fun I hI => by
      rw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp,
        LinearMap.coe_comp, LinearMap.coe_comp]
      exact ((ConcreteCategory.bijective_of_isIso (e.inv.app I)).comp (hγ I)).comp (hθ I hI)
  exact ⟨K, φ, hK, hφ⟩

end GlobalTheory.Cohom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveCechComplexLineBundleStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_finite_projective_cechComplex_lineBundle : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → Smooth f → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechLB f M (fun i => nonzeroLocus (s i))), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  first | exact @GlobalTheory.Cohom.exists_finite_projective_complex_cechLB | exact GlobalTheory.Cohom.exists_finite_projective_complex_cechLB | (intros; apply GlobalTheory.Cohom.exists_finite_projective_complex_cechLB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineChartsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.veryAmple_compact_quasiSeparated_affine_charts : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ ∀ I : Finset (Fin (m + 1)), I.Nonempty → IsAffineOpen (⨅ i ∈ I, nonzeroLocus (s i)) := by
  first | exact @GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen | exact GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen | (intros; apply GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem nonempty_perf_of_smooth_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M) := by
  intro R _ X f hf hp M hM
  obtain ⟨H, hH, m, s, hs⟩ := hp
  obtain ⟨K, φ, hK⟩ := GlobalTheory.T.exists_finite_projective_cechComplex_lineBundle R X f H m s M hH hM hs hf
  exact GlobalTheory.T.threeTermComplex_of_projective_cech_model R X f M (Fin (m + 1)) (fun i => nonzeroLocus (s i)) K φ hM hs.1
    (GlobalTheory.T.veryAmple_compact_quasiSeparated_affine_charts R X f H m s hH hs).2.2 hK

end GlobalTheory.AbLaw
end
end
