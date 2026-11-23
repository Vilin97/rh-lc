module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator

section

@[expose] public section

namespace GlobalTheory.CommonDenominatorLemma

open NumberField

theorem exists_common_denominator {E : Type} [inst : Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : Submodule.FG L) :
    ∃ (b : NumberField.RingOfIntegers E), b ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ x ∈ L, ∀ (i : Fin N), ∃ (u : NumberField.RingOfIntegers E), (↑u : E) = (↑b : E) * x i := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin N → E) × Fin N =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let b : NumberField.RingOfIntegers E :=
    ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin N)), ((z p).2 : NumberField.RingOfIntegers E)
  refine ⟨b, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, i) ∈ s ×ˢ (Finset.univ : Finset (Fin N)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ i⟩)
    refine ⟨e * (z (g, i)).1, ?_⟩
    have h := hz (g, i)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show b = ((z (g, i)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro i
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    obtain ⟨c2, h2⟩ := hy i
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SelfDualIdDecomp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_mem_range (a : 𝓞 E) : star (a : E) ∈ (algebraMap (𝓞 E) E).range := by
  have h : IsIntegral ℤ (star (a : E)) := by
    exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨star (a : E), h⟩, rfl⟩

theorem exists_den {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hfg : L.FG) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ ∀ x ∈ L, ∀ i, ∃ u : 𝓞 E, (u : E) = (b : E) * x i := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator ..)

theorem exists_extension {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L)
    (φ : L →ₗ[𝓞 E] 𝓞 E) : ∃ u ∈ L, ∀ x (hx : x ∈ L), stdH E N u x = (φ ⟨x, hx⟩ : E) := by
  classical
  obtain ⟨hfg, -, hdual⟩ := hL
  obtain ⟨b, hb0, hb⟩ := exists_den L hfg
  obtain ⟨c', hc'⟩ := star_mem_range b
  have hbE : (b : E) ≠ 0 := by
    intro h; apply hb0; exact RingOfIntegers.coe_injective (by simpa using h)
  have hc0 : star (b : E) ≠ 0 := star_ne_zero.2 hbE
  have hce : ∀ i, (Pi.single i (star (b : E)) : Fin N → E) ∈ L := by
    intro i
    rw [hdual]
    intro x hx
    obtain ⟨u, hu⟩ := hb x hx i
    have h1 : stdH E N x (Pi.single i (star (b : E))) = star (u : E) := by
      rw [hu, star_mul]
      simp [stdH, Pi.single_apply]
    rw [h1]; exact star_mem_range u
  let w : Fin N → E := fun i => (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) / star (b : E)
  have hw : ∀ x (hx : x ∈ L), (φ ⟨x, hx⟩ : E) = ∑ i, w i * x i := by
    intro x hx
    choose ub hub using hb x hx
    have h1 : (b * c') • (⟨x, hx⟩ : L) = ∑ i, ub i • (⟨Pi.single i (star (b : E)), hce i⟩ : L) := by
      apply Subtype.ext; funext j
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have := hub j
      simp only [map_mul, hc']
      rw [show (algebraMap (𝓞 E) E) (ub j) = (b : E) * x j from this]
      ring
    have h2 := congrArg (fun z => ((φ z : 𝓞 E) : E)) h1

    simp only [map_smul, map_sum, smul_eq_mul] at h2
    push_cast at h2
    apply mul_left_cancel₀ (mul_ne_zero hbE hc0)
    have h3 : (b : E) * star (b : E) * (φ ⟨x, hx⟩ : E) =
        ∑ i, ((ub i : 𝓞 E) : E) * (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) := by
      rw [← h2, ← hc']
    rw [h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hub i]
    simp only [w]
    first | (field_simp; ring) | field_simp
  refine ⟨fun i => star (w i), ?_, ?_⟩
  · rw [hdual]
    intro y hy
    have : stdH E N y (fun i => star (w i)) = star (φ ⟨y, hy⟩ : E) := by
      rw [hw y hy, star_sum]
      simp [stdH, star_mul, mul_comm]
    rw [this]; exact star_mem_range _
  · intro x hx
    rw [hw x hx]
    simp [stdH]

theorem exists_decomp {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L) :
    ∃ (r : ℕ) (s u : Fin r → Fin N → E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  classical
  have hspan := hL.2.1
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  choose u hu hux using fun k : Fin m => exists_extension L hL ((LinearMap.proj k) ∘ₗ g)
  refine ⟨m, fun k => (f (Pi.single k 1) : Fin N → E), u, fun k => (f _).2, hu, ?_⟩
  have hrec : ∀ y : L, (y : Fin N → E) = ∑ k, ((g y k : 𝓞 E) : E) • (f (Pi.single k 1) : Fin N → E) := by
    intro y
    have h1 : f (g y) = y := LinearMap.congr_fun hfg y

    conv_lhs => rw [← h1, pi_eq_sum_univ' (g y), map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on hspan
  rintro x hx
  rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
  funext i
  have e1 : x i = ∑ k, ((g ⟨x, hx⟩ k : 𝓞 E) : E) * (f (Pi.single k 1) : Fin N → E) i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : L) : Fin N → E) from rfl, hrec ⟨x, hx⟩]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun k _ => Algebra.smul_def _ _
  rw [e1]
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, vecMulVec_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hux k x hx
  simp only [stdH, LinearMap.comp_apply, LinearMap.proj_apply] at this
  rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply]
  ring

theorem iddecomp : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  intro D N L hL
  exact exists_decomp L hL

end GlobalTheory.SelfDualIdDecomp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.self_dual_lattice_resolution_of_identity : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧ ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  first | exact @GlobalTheory.SelfDualIdDecomp.iddecomp | exact GlobalTheory.SelfDualIdDecomp.iddecomp | (intros; apply GlobalTheory.SelfDualIdDecomp.iddecomp <;> assumption)
end
end
