module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KapEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.QuadMu
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.TnOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormEqOne

section

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk14.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qk14.norm_eq_one :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x : UpperTheory.Reformulated.B.Qk14.Qbar l},
      ‖x - (1 : UpperTheory.Reformulated.B.Qk14.Qbar l)‖ < (1 : ℝ) → ‖x‖ = (1 : ℝ) := by
  intro l _ x h
  have hne : ‖x - 1‖ ≠ ‖(1 : UpperTheory.Reformulated.B.Qk14.Qbar l)‖ := by
    rw [norm_one]
    exact h.ne
  have key := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [sub_add_cancel, norm_one] at key
  rw [key]
  exact max_eq_right h.le
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PKapEx

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace KapEx

theorem norm_eq_one {l : ℕ} [Fact l.Prime] {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 :=
  _root_.UpperTheory.Reformulated.B.Qk14.norm_eq_one h

def W (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {a | ‖(a : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    have e : (a : Qbar l) * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ha)
    rw [norm_mul, norm_eq_one ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have ha0 : (a : Qbar l) ≠ 0 := a.ne_zero
    have e : ((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((a : Qbar l)⁻¹ * (a - 1)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ ha0, mul_one]
      ring
    rw [e, norm_neg, norm_mul, norm_inv, norm_eq_one ha, inv_one, one_mul]
    exact ha

theorem isOpen_kappaOpenNeighbourhood (l : ℕ) [Fact l.Prime] : IsOpen ((W l : Subgroup (Qbar l)ˣ) : Set (Qbar l)ˣ) := by
  show IsOpen {a : (Qbar l)ˣ | ‖(a : Qbar l) - 1‖ < 1}
  exact isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

theorem cong_of_mem {l : ℕ} [Fact l.Prime] {x : (Qbar l)ˣ} (hx : x ∈ W l) : Cong x 1 := by
  unfold Cong
  rw [Units.val_one]
  exact hx

theorem exists_pow_cong {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {l : ℕ} [Fact l.Prime] (f : Γ →* (Qbar l)ˣ) (hf : Continuous f) : ∃ d : ℕ, 0 < d ∧ ∀ g, f g ^ d ∈ W l := by
  have hU : IsOpen (((W l).comap f : Subgroup Γ) : Set Γ) := (isOpen_kappaOpenNeighbourhood l).preimage hf
  haveI := Subgroup.quotient_finite_of_isOpen _ hU
  have hi : ((W l).comap f).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨((W l).comap f).index.factorial, Nat.factorial_pos _, fun g => ?_⟩
  rw [← map_pow]
  exact Subgroup.pow_mem_of_index_ne_zero_of_dvd hi g fun n h0 hn => Nat.dvd_factorial h0 hn

theorem cc_notMem {Ω : Type} [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [_root_.NumberField.IsTotallyComplex K]
    {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm

end KapEx

end UpperTheory.V.Cu2

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPKapEx

section

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace KapEx
end KapEx
open UpperTheory.V.Cu2.KapEx in
theorem kapEx_alt (h1 : TwistIne) (h2 : AlgType) : _root_.UpperTheory.V.Cu2.KapExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK2 hTC hld hsp hcc
  obtain ⟨cc, hcc⟩ := hcc
  have : IsTotallyComplex K' := hTC
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  have : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  obtain ⟨κ₀, htw⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K' Ω hK2 l hl2 hld ι cc hcc
  obtain ⟨art, Y, a, τ, hart, hYa, hL, ha1, ha0, -⟩ := htw.alg
  obtain ⟨mo, hmo0, -, hmo⟩ := htw.ord
  have hi : (galOf ℚ K' Ω).index = 2 := (galEmbTop ℚ K' Ω).2.2.trans hK2
  have hccK : cc ∉ galOf ℚ K' Ω := cc_notMem K' hcc
  have hfix : ∀ t : G ℚ Ω, t ∈ K'.fixingSubgroup → t ∈ galOf ℚ K' Ω := fun t h =>
    (mem_galOf ℚ K' Ω).2 fun x => (IntermediateField.mem_fixingSubgroup_iff K' t).1 h x x.2
  have hIne : ∀ (A : ValuationSubring Ω) (h : G K' Ω), resQ K' h ∈ Ine (F := ℚ) A → h ∈ Ine (F := K') A :=
    fun A h hh => ⟨hh.1, hh.2⟩
  have hεc : Continuous (cycBar K' Ω l) := by
    have hf : Continuous (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom : ℤ_[l] → Qbar l) :=
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact (Units.continuous_map hf).comp (continuous_cycZ K' Ω l)
  have hεunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ h ∈ Ine (F := K') A, cycBar K' Ω l h = 1 := by
    intro A hA h hh
    have e : cycZ K' Ω l h = 1 := MonoidHom.mem_ker.1 (((places K' Ω l A).2.2.2 hA) hh)
    simp only [cycBar, MonoidHom.comp_apply, e, map_one]
  have hεres : ∀ h : G K' Ω, cycBar K' Ω l h = cycBar ℚ Ω l (resQ K' h) := fun h => rfl
  have hlam : ∀ h : G K' Ω, (κ₀ ^ 2 * cycBar K' Ω l) h = κ₀ h ^ 2 * cycBar K' Ω l h := fun h => by
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply]
  have hlamc : Continuous ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) := by
    have e : ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) = fun h => κ₀ h ^ 2 * cycBar K' Ω l h := funext hlam
    rw [e]
    exact (htw.cont.pow 2).mul hεc
  obtain ⟨d, hd0, hd⟩ := exists_pow_cong _ hlamc
  refine ⟨d * mo, (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo), fun j hj => ?_⟩
  rw [← pow_mul]
  have hN : 0 < d * mo * j := Nat.mul_pos (Nat.mul_pos hd0 hmo0) (by omega)
  obtain ⟨Y', hY', hL'⟩ := h2 K' Ω l ι art Y a κ₀ hart hYa hL (2 * (d * mo * j)) (d * mo * j)
  have hpw : (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) =
      κ₀ ^ (2 * (d * mo * j)) * cycBar K' Ω l ^ (d * mo * j) := by
    rw [mul_pow, ← pow_mul]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ⇑((κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) : G K' Ω →* (Qbar l)ˣ) = fun h => (κ₀ h ^ 2 * cycBar K' Ω l h) ^ (d * mo * j) :=
      funext fun h => by rw [MonoidHom.pow_apply, hlam]
    rw [e]
    exact ((htw.cont.pow 2).mul hεc).pow _
  · refine ⟨art, Y', _, τ, hart, hY', by rw [hpw]; exact hL', ?_, ?_⟩
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a τ + ((d * mo * j : ℕ) : ℤ) = -((d * mo * j : ℕ) : ℤ)
      rw [ha1]
      push_cast
      ring
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a (ComplexEmbedding.conjugate τ) + ((d * mo * j : ℕ) : ℤ) = ((d * mo * j : ℕ) : ℤ)
      rw [ha0]
      push_cast
      ring
  · intro t ht h h' hh'
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have hu : cc⁻¹ * t ∈ galOf ℚ K' Ω := by
      rw [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
      exact iff_of_false hccK htg
    rw [← range_galEmb] at hu
    obtain ⟨v, hv⟩ := hu
    have hh'' : galEmb ℚ K' Ω h' = t * galEmb ℚ K' Ω h * t⁻¹ := hh'
    have hs : galEmb ℚ K' Ω h' = cc * galEmb ℚ K' Ω (v * h * v⁻¹) * cc⁻¹ := by
      rw [map_mul, map_mul, map_inv, hv, hh'']
      group
    have hc := htw.conj (v * h * v⁻¹) h' hs
    simp only [map_mul, map_inv, mul_inv_cancel_comm] at hc
    have hε' : cycBar K' Ω l h' = cycBar K' Ω l h := by
      rw [hεres, hεres h, hh', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ← mul_pow, hlam, hlam, hε', mul_mul_mul_comm, ← mul_pow, hc,
      ← sq (cycBar K' Ω l h), inv_pow, inv_mul_cancel, one_pow]
  · intro t ht h hh
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have e1 := htw.ver h t htg hh
    have e2 : cycBar K' Ω l h = cycBar ℚ Ω l t * cycBar ℚ Ω l t := by
      rw [hεres, hh, map_mul]
    rw [MonoidHom.pow_apply, hlam, e1, e2, neg_sq, inv_pow, ← sq (cycBar ℚ Ω l t), inv_mul_cancel, one_pow]
  · intro h
    apply cong_of_mem
    rw [MonoidHom.pow_apply, pow_mul, pow_mul]
    exact pow_mem (pow_mem (hd h) mo) j
  · intro A hA h hh
    have h' := hIne A h hh
    rw [MonoidHom.pow_apply, hlam, hεunr A hA h h', mul_one, ← pow_mul,
      show 2 * (d * mo * j) = mo * (2 * d * j) by ring, pow_mul, hmo A hA h h', one_pow]
  · intro A hA
    rcases h1 Ω l ι K' hK2 hTC hld hsp cc κ₀ htw A hA with e | e
    · refine Or.inr fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), zpow_neg, zpow_natCast, sq, mul_assoc, inv_mul_cancel, mul_one,
        inv_pow]
    · refine Or.inl fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), one_pow, one_mul, zpow_natCast]
end UpperTheory.V.Cu2
end
end
end
end
