module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.ClassCover

variable {L : Type} [Field L] [NumberField L]

def toIdeles : (FiniteAdeleRing (𝓞 L) L)ˣ →* Neutral.B1.Ideles L :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem eq_diag_mul_of_classOf (y : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles y) = 1) :
    ∃ (k : Lˣ) (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((u : FiniteAdeleRing (𝓞 L) L) P) = 1) ∧
      y = Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom k * u := by
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 L) L).2, ((u⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2, ?_, ?_⟩,
    fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((toIdeles y : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 =
        ((Neutral.B1.diagUnits L k * u : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 := by rw [he]
    exact h2

end GlobalTheory.ClassCover
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PClassFin

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open scoped Pointwise

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem exists_cover_units (E : Type) [Field E] [NumberField E] (O : Subgroup (Af E)ˣ)
    (hO : IsOpen (O : Set (Af E)ˣ)) :
    ∃ F : Finset (Af E)ˣ, ∀ u ∈ GroundTheory.Global.finiteIntegralUnits E, ∃ f ∈ F, ∃ o ∈ O, u = f * o := by
  obtain ⟨t, ht⟩ := (GroundTheory.Global.isCompact_finiteIntegralUnits E).elim_finite_subcover
    (fun a : (Af E)ˣ => a • (O : Set (Af E)ˣ)) (fun a => hO.smul a)
    (fun c _ => Set.mem_iUnion.2 ⟨c, Set.mem_smul_set.2 ⟨1, one_mem O, mul_one c⟩⟩)
  refine ⟨t, fun u hu => ?_⟩
  obtain ⟨f, hf, huf⟩ := Set.mem_iUnion₂.1 (ht hu)
  obtain ⟨o, ho, rfl⟩ := Set.mem_smul_set.1 huf
  exact ⟨f, hf, o, ho, rfl⟩

private theorem mem_units_of_valued (E : Type) [Field E] [NumberField E] (u : (Af E)ˣ)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : Af E) P) = 1) :
    u ∈ GroundTheory.Global.finiteIntegralUnits E := by
  refine (GroundTheory.Global.mem_finiteIntegralUnits E).2 fun P => ⟨(hu P).le, ?_⟩
  have e : (((u⁻¹ : (Af E)ˣ) : Af E) P) * ((u : Af E) P) = 1 :=
    congrArg (fun t : Af E => t P) (Units.inv_mul u)
  have e2 := congrArg Valued.v e
  rw [map_mul, hu P, mul_one, map_one] at e2
  exact e2.le

theorem pClassFin_of : ClassFin := by
  intro E _ _ O hO
  classical
  obtain ⟨F, hF⟩ := exists_cover_units E O hO
  let ψ : (Af E)ˣ →* ClassGroup (𝓞 E) :=
    (ReciprocityTheory.Neutral.Bridge.HCFR.classOf E).comp GlobalTheory.ClassCover.toIdeles
  let sel : ClassGroup (𝓞 E) → (Af E)ˣ := fun c => if h : ∃ y, ψ y = c then h.choose else 1
  have hsel : ∀ y, ψ (sel (ψ y)) = ψ y := by
    intro y
    have h : ∃ z, ψ z = ψ y := ⟨y, rfl⟩
    simp only [sel, dif_pos h]
    exact h.choose_spec
  refine ⟨(Finset.univ.image sel ×ˢ F).image (fun p => p.1 * p.2), fun y => ?_⟩
  have hk : ψ ((sel (ψ y))⁻¹ * y) = 1 := by rw [map_mul, map_inv, hsel, inv_mul_cancel]
  obtain ⟨k, u, hu, he⟩ := GlobalTheory.ClassCover.eq_diag_mul_of_classOf _ hk
  obtain ⟨f, hf, o, ho, rfl⟩ := hF u (mem_units_of_valued E u hu)
  refine ⟨sel (ψ y) * f, Finset.mem_image.2 ⟨(sel (ψ y), f), Finset.mem_product.2
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hf⟩, rfl⟩, o, ho, k, ?_⟩
  have hy : y = sel (ψ y) * (diagF E k * (f * o)) := by
    rw [show diagF E k * (f * o) = (sel (ψ y))⁻¹ * y from he.symm, mul_inv_cancel_left]
  calc y = sel (ψ y) * (diagF E k * (f * o)) := hy
    _ = sel (ψ y) * f * o * diagF E k := by
      rw [mul_comm (diagF E k), ← mul_assoc, ← mul_assoc]

end UpperTheory.Gal.CertificateRingHomMap
end
end
