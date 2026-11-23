module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafPresheafOverCoproductEqSumStatement
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
public import Mathlib.AlgebraicGeometry.Scheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijective

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem coh_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  intro R _ F U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F (sch.obj U) ι (fun i => sch.obj (V i)) (fun i => sch.map (j i)) ?_ n
  intro k
  exact GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U ι V j hc (yoneda.obj U) (𝟙 _) (fun i => yoneda.obj (V i)) (fun i => yoneda.map (j i))
    (fun _ => 𝟙 _) (fun i => IsPullback.of_vert_isIso (by simp))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijectiveStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  first | (exact @GlobalTheory.coh_coprod_bijective) | (exact GlobalTheory.coh_coprod_bijective) | (intros; apply GlobalTheory.coh_coprod_bijective  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquivStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i ↦ Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  first | exact @GlobalTheory.EtC.spec_pi_cofan_isColimit | exact GlobalTheory.EtC.spec_pi_cofan_isColimit | (intros; apply GlobalTheory.EtC.spec_pi_cofan_isColimit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acycF_of_pi_sh : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type)
    [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) →
    AcycF R (sp B) F := by
  intro R _ F ι _ T _ B _ ⟨e⟩ hT n hn
  obtain ⟨hc⟩ := GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv ι T B e
  have hbij := GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective R F (Spec (CommRingCat.of B)) ι (fun i => Spec (CommRingCat.of (T i)))
    (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))) hc n
  have hsub : ∀ i, Subsingleton (H R (sch.obj (Spec (CommRingCat.of (T i)))) F n) :=
    fun i => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf R (T i) (hT i) F n hn
  refine ⟨fun x y => hbij.1 ?_⟩
  funext i
  exact Subsingleton.elim _ _

end GlobalTheory.EtC
end
end
