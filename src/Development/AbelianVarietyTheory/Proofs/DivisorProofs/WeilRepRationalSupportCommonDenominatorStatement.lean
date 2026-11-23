module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDiv
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeighStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLatticeStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

theorem _root_.GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  first | exact @GlobalTheory.FinSuppHeis.heis_fix_finDiv | exact GlobalTheory.FinSuppHeis.heis_fix_finDiv | (intros; apply GlobalTheory.FinSuppHeis.heis_fix_finDiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix nonZeroDivisors

noncomputable section
namespace GlobalTheory.FinSupp

theorem exists_den_of_trace_int (F : Type) [Field F] [NumberField F] :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ t : F, (∀ a : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F ((a : F) * t) = m) →
      IsIntegral ℤ ((D : F) * t) := by
  classical
  obtain ⟨c, hc, hfr⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, fun t ht => ?_⟩
  · rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · have hmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        first | exact one_ne_zero | simp | exact FractionalIdeal.one_ne_zero
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨m, hm⟩ := ht b
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, hm]
      simp
    obtain ⟨y, hy⟩ := hfr t hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) * t = ((e * y : 𝓞 F) : F) := by
      have h1 : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) = ((e : F) * (c : F)) := by
        have := congrArg (fun z : 𝓞 F => (z : F)) he
        simp only [map_mul, map_natCast] at this
        rw [← this]
      rw [h1, mul_assoc]
      have h2 : (y : F) = (c : F) * t := by
        rw [show (y : F) = algebraMap (𝓞 F) F y from rfl, hy, Algebra.smul_def]
      push_cast
      first | rw [h2] | rw [← h2] | exact congrArg (_ * ·) h2.symm | simp [h2]
    rw [this]
    exact (e * y).isIntegral_coe

theorem trace_int_of_finPart {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (s : F)
    (hs : ψ (finPart F (algebraMap F (AF F) s)) = 1) : ∃ m : ℤ, Algebra.trace ℚ F s = m := by
  set x : AF F := algebraMap F (AF F) s with hx
  set z : AF F := x - finPart F x with hzdef
  have hz : At (evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := by
      apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
      rw [map_zero]
      exact hu
    show u * z = 0
    refine Prod.ext ?_ ?_
    · change u.1 * (x.1 - (0 : Ainf F)) = 0
      rw [hu1, zero_mul]
    · change u.2 * (x.2 - x.2) = 0
      rw [sub_self, mul_zero]
  have hψz : ψ z = 1 := by
    have h := hψ.2.1 s
    rw [← hx, show x = z + finPart F x by rw [hzdef, sub_add_cancel], AddChar.map_add_eq_mul, hs, mul_one] at h
    exact h
  have hev : evI F z = mixedEmbedding F s := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x.1 - 0) = _
    rw [sub_zero, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rfl
  have h := hψ.2.2 z hz
  rw [hψz, hev, GlobalTheory.LatVacArith.trace_mixedEmbedding] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h.symm
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hq : (((Algebra.trace ℚ F s : ℚ) : ℝ) : ℂ) = -(n : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -hn
  refine ⟨-n, ?_⟩
  push_cast
  exact_mod_cast hq

end GlobalTheory.FinSupp

namespace GlobalTheory.FinSupp.DenStd

theorem exists_den : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  intro F _ _
  obtain ⟨D, hD, hint⟩ := GlobalTheory.FinSupp.exists_den_of_trace_int F
  exact ⟨D, hD, fun ψ hψ t ht => hint t fun a => GlobalTheory.FinSupp.trace_int_of_finPart hψ _ (ht a)⟩

end GlobalTheory.FinSupp.DenStd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivialStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

theorem _root_.GlobalTheory.T.exists_bounded_denominator_standardChar_trivial : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  first | exact @GlobalTheory.FinSupp.DenStd.exists_den | exact GlobalTheory.FinSupp.DenStd.exists_den | (intros; apply GlobalTheory.FinSupp.DenStd.exists_den <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominator

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.FinSupp

theorem finDiv_finPart_mul {F : Type} [Field F] [NumberField F] {N m : ℕ} {T : AF F} (hT : GlobalTheory.FinSupp.FinDiv F N ((m : AF F) * T))
    (a : 𝓞 F) : GlobalTheory.FinSupp.FinDiv F N (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) * T) := by
  intro v
  obtain ⟨b, hb, e⟩ := hT v
  have ha : algebraMap F (Fv F v) (a : F) ∈ v.adicCompletionIntegers F := HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
  refine ⟨algebraMap F (Fv F v) (a : F) * b, mul_mem ha hb, ?_⟩
  have e1 : evFin F v (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F)))) =
      evFin F v (algebraMap F (AF F) ((m : F) * (a : F))) := rfl
  rw [map_mul, e1, AlgHom.commutes, map_mul, map_natCast]
  simp only [map_mul, map_natCast] at e
  rw [mul_comm ((m : Fv F v)) _, mul_assoc, e]
  ring

theorem finPart_mul {F : Type} [Field F] [NumberField F] (x y : AF F) :
    GlobalTheory.FinSupp.finPart F x * y = GlobalTheory.FinSupp.finPart F (x * y) :=
  Prod.ext (zero_mul _) rfl

theorem exists_common_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N, hN1, hinv⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights F E n d (Fin n × Fin d) M.co.e N hN1
  obtain ⟨D, hD1, hD⟩ := GlobalTheory.T.exists_bounded_denominator_standardChar_trivial F
  refine ⟨D * C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC g.1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC (by positivity)
  · intro ξ hξ i
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin n × Fin d → AF F := c • Pi.single i 1 with hy
      set w' := M.co.e.symm (0, y) with hw'
      set p : UA σ X.J × UA σ W.J := (g, h) with hp
      set w := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w = c • M.co.e ((((g.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          M.co.e.symm (0, Pi.single i 1) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hy, hp]
        rw [show ((0 : Fin n × Fin d → AF F), c • Pi.single i (1 : AF F)) = c • ((0 : Fin n × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h2 a
      have himpl := S.impl p w Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, hp]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have hx := congrFun himpl (fun j => algebraMap F (AF F) (ξ j))
      simp only [Darboux.rho, hw', LinearEquiv.apply_symm_apply, schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ ((fun j => algebraMap F (AF F) (ξ j)) ⬝ᵥ y) = 1 := by
        have hne : om p Φ (fun j => algebraMap F (AF F) (ξ j)) ≠ 0 := hξ
        exact (mul_eq_right₀ hne).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, finPart_mul, ← map_mul] at h1
      convert h1 using 3
      ring
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.FinSupp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominatorStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.weilRep_rational_support_common_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  first | exact @GlobalTheory.FinSupp.exists_common_denominator | exact GlobalTheory.FinSupp.exists_common_denominator | (intros; apply GlobalTheory.FinSupp.exists_common_denominator <;> assumption)
end
end
