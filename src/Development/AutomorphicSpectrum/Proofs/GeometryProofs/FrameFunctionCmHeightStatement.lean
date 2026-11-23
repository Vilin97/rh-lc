module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosedStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGramStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferentStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNormStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDualStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLeStatement
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureTypeLatticesOrthogonalStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpenStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbeddingStatement
import Mathlib.Algebra.Ring.IsFormallyReal

-- Source module: Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointShiftStOfPlaceShiftSt

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.PlaceShiftModel

open NumberField IsDedekindDomain GlobalTheory.CompHt GlobalTheory.HTLat

variable {E : Type} [Field E] [NumberField E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem norm_le_one (τ : E →+* ℂ_[ℓ]) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  rw [← algebraMap_embO (PadicComplexInt.integers ℓ) τ a]
  exact (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 (Subtype.prop _)

theorem norm_ell : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] ℂ_[ℓ]), norm_algebraMap']
  exact Padic.norm_p_lt_one

end GlobalTheory.FlatCM.PlaceShiftModel

end
end
end

-- Source module: Development.WeilBound.CoreStatements.SesquilinearFractions.DTransUnit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem transition_matrix_unique {I : Type} [Fintype I] [DecidableEq I] (e : I → D.La) (he : LinearIndependent (𝓞 E) e)
    (C : Matrix I I E) (hC : ∀ m y, ∑ n, C m n * sesq D (e n) y = 0) : C = 0 := by
  classical
  ext m k
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (Finset.univ.image (C m))
  choose u hu using fun n => hc (C m n) (Finset.mem_image_of_mem (C m) (Finset.mem_univ n))
  have hc0 : ((c : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero c
  have huv : ∀ n, (u n : E) = (c : 𝓞 E) * C m n := fun n => by
    rw [show ((u n : 𝓞 E) : E) = algebraMap (𝓞 E) E (u n) from rfl, hu n, Algebra.smul_def]
  set z : D.La := ∑ n, u n • e n with hz
  have hz0 : ∀ y, sesq D y z = 0 := by
    intro y
    have h1 : sesq D z y = 0 := by
      rw [hz, sesq_sum_smul_left]
      simp_rw [huv]
      calc ∑ n, (c : 𝓞 E) * C m n * sesq D (e n) y = (c : 𝓞 E) * ∑ n, C m n * sesq D (e n) y := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
        _ = 0 := by rw [hC m y, mul_zero]
    rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 z y, h1, map_zero, neg_zero]
  have hzz : z = 0 := (GlobalTheory.T.sesq_unimodular_dual E H D).1 z hz0
  have hu0 := (Fintype.linearIndependent_iff.1 he) u (by rw [← hz]; exact hzz)
  have : (c : 𝓞 E) * C m k = 0 := by rw [← huv, hu0 k]; simp
  simpa [hc0] using this

theorem isTransition_of_coefficients {I : Type} [Fintype I] (x e : I → D.La) (m : ℕ) (hm : 0 < m) (S : Matrix I I (𝓞 E))
    (hS : ∀ a, m • x a = ∑ b, S a b • e b) :
    IsTransition D x e (Matrix.of fun a b => (S a b : E) / m) := by
  intro a y
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have h := congrArg (fun z => sesq D z y) (hS a)
  rw [sesq_sum_smul_left, ← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1] at h
  apply mul_left_cancel₀ hm0
  have h' : (m : E) * sesq D (x a) y = ∑ b, (S a b : E) * sesq D (e b) y := by simpa using h
  rw [h', Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.of_apply]
  field_simp

end

theorem padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  intro E _ _ _ H D I _ _ x e T ℓ hx he hT j
  classical
  have : Fact (Nat.Prime ℓ) := ⟨ℓ.2⟩
  obtain ⟨hxi, n0, hn0, hspx⟩ := hx
  obtain ⟨hei, m0, hm0, hspe⟩ := he
  have hm0p : 0 < m0 := Nat.pos_of_ne_zero fun h => hm0 (h ▸ dvd_zero _)
  have hn0p : 0 < n0 := Nat.pos_of_ne_zero fun h => hn0 (h ▸ dvd_zero _)
  choose S hS using fun a => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspe (x a))
  choose R hR using fun b => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspx (e b))
  have hT1 := isTransition_of_coefficients D x e m0 hm0p (Matrix.of S) fun a => (hS a).symm
  have hT2 := isTransition_of_coefficients D e x n0 hn0p (Matrix.of R) fun b => (hR b).symm
  set T1 : Matrix I I E := Matrix.of fun a b => ((Matrix.of S) a b : E) / m0
  set T2 : Matrix I I E := Matrix.of fun a b => ((Matrix.of R) a b : E) / n0

  have hTT1 : T = T1 := by
    have := transition_matrix_unique D e hei (T - T1) fun m y => by
      calc ∑ n, (T - T1) m n * sesq D (e n) y = ∑ n, T m n * sesq D (e n) y - ∑ n, T1 m n * sesq D (e n) y := by
            rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _ => by rw [Matrix.sub_apply, sub_mul]
        _ = 0 := by rw [← hT m y, ← hT1 m y, sub_self]
    exact sub_eq_zero.1 this

  have hTT2 : T2 * T = 1 := by
    have := transition_matrix_unique D e hei (T2 * T - 1) fun b y => by
      have hsum : ∑ n, (T2 * T) b n * sesq D (e n) y = sesq D (e b) y := by
        rw [hT2 b y]
        calc ∑ n, (T2 * T) b n * sesq D (e n) y = ∑ n, ∑ c, T2 b c * T c n * sesq D (e n) y := by
              refine Finset.sum_congr rfl fun n _ => ?_; rw [Matrix.mul_apply, Finset.sum_mul]
          _ = ∑ c, T2 b c * ∑ n, T c n * sesq D (e n) y := by
              rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
          _ = ∑ c, T2 b c * sesq D (x c) y := Finset.sum_congr rfl fun c _ => by rw [hT c y]
      have hone : ∑ n, (1 : Matrix I I E) b n * sesq D (e n) y = sesq D (e b) y := by
        rw [Finset.sum_eq_single b]
        · rw [Matrix.one_apply_eq, _root_.one_mul]
        · intro n _ hn; rw [Matrix.one_apply_ne (Ne.symm hn), MulZeroClass.zero_mul]
        · simp
      calc ∑ n, (T2 * T - 1) b n * sesq D (e n) y
            = ∑ n, (T2 * T) b n * sesq D (e n) y - ∑ n, (1 : Matrix I I E) b n * sesq D (e n) y := by
              rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _ => by rw [Matrix.sub_apply, sub_mul]
        _ = 0 := by rw [hsum, hone, sub_self]
    exact sub_eq_zero.1 this

  have hnat : ∀ k : ℕ, ¬ (ℓ : ℕ) ∣ k → ‖((k : ℕ) : ℂ_[ℓ])‖ = 1 := by
    intro k hk
    have hcop : Nat.Coprime k ℓ := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd ℓ.2).2 hk))
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + b * ℓ = 1 := by
      refine ⟨Nat.gcdA k ℓ, Nat.gcdB k ℓ, ?_⟩
      have := Nat.gcd_eq_gcd_ab k ℓ
      rw [hcop] at this
      push_cast at this
      linarith
    have h1 : ((a : ℂ_[ℓ]) * k + (b : ℂ_[ℓ]) * ℓ) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : ℂ_[ℓ])) hab
    have hle : ‖((k : ℕ) : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    have ha : ‖(a : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
    have hb : ‖(b : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
    have hl := GlobalTheory.FlatCM.PlaceShiftModel.norm_ell (ℓ := (ℓ : ℕ))
    have hmax := IsUltrametricDist.norm_add_le_max ((a : ℂ_[ℓ]) * k) ((b : ℂ_[ℓ]) * ℓ)
    rw [h1, norm_one, norm_mul, norm_mul] at hmax
    have hbl : ‖(b : ℂ_[ℓ])‖ * ‖((ℓ : ℕ) : ℂ_[ℓ])‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hb) hl
    rcases le_max_iff.1 hmax with h | h
    · have : 1 ≤ ‖((k : ℕ) : ℂ_[ℓ])‖ := le_trans h (mul_le_of_le_one_left (norm_nonneg _) ha)
      exact le_antisymm hle this
    · exact absurd h (not_le.2 hbl)
  have hentry : ∀ (A : Matrix I I (𝓞 E)) (k : ℕ), ¬ (ℓ : ℕ) ∣ k → ∀ a b,
      ‖j (((Matrix.of fun a b => ((A a b : 𝓞 E) : E) / k) : Matrix I I E) a b)‖ ≤ 1 := by
    intro A k hk a b
    simp only [Matrix.of_apply, map_div₀, map_natCast, norm_div, hnat k hk, div_one]
    exact GlobalTheory.FlatCM.PlaceShiftModel.norm_le_one j (A a b)
  have hdet : ∀ M : Matrix I I E, (∀ a b, ‖j (M a b)‖ ≤ 1) → ‖j M.det‖ ≤ 1 := by
    intro M hM
    rw [RingHom.map_det]
    have := GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] I (M.map j) 1 zero_le_one (fun a b => hM a b)
    simpa using this
  have h1 : ‖j T.det‖ ≤ 1 := by rw [hTT1]; exact hdet _ (hentry (Matrix.of S) m0 hm0)
  have h2 : ‖j T2.det‖ ≤ 1 := hdet _ (hentry (Matrix.of R) n0 hn0)
  have hprod : ‖j T2.det‖ * ‖j T.det‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Matrix.det_mul, hTT2, Matrix.det_one, map_one, norm_one]
  nlinarith [norm_nonneg (j T.det), norm_nonneg (j T2.det)]

end PositivityTheory.Xgf
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  first | exact @PositivityTheory.Xgf.padic_norm_transition_det_one | exact PositivityTheory.Xgf.padic_norm_transition_det_one
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | exact GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | (intros; apply GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeight

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem flatGen_finNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (ℓ : Nat.Primes), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → ∃ t : E, (∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ + Real.log ‖j (IsCMField.complexConj E t)‖ + Real.log ‖j (gramE (FU.Di i) e).det‖ = -((D.p : ℝ) + D.q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧ (IsLocBasis (𝓞 E) ℓ e → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ = 0) ∧ ∀ (j : k →+* ℂ_[ℓ]) (t₀ : ℝ), HasFinNorm U τ φ ℓ (j.comp (IntermediateField.inclusion hc).toRingHom) t₀ → t₀ = Real.log ‖j r‖ - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) t)‖ - D.q * logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((D.q : ℝ) - D.p) * (logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (H.rt : E))‖) := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r ℓ hty hrt hmem hline he hconst hr hz
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hxl, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ℓ k inferInstance hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he
  have hT0 : T.det ≠ 0 := hdet hxl.1
  have hge : (gramE (FU.Di i) e).det ≠ 0 := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  have hconj : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
    (AlgEquiv.map_det (IsCMField.complexConj E) T).symm
  have hgdet : (gramE (FU.Di i) x).det
      = T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hconj]
  refine ⟨T.det, ?_, ?_, ?_⟩
  · intro j
    have h1 := GlobalTheory.T.gram_determinant_log_different E H (FU.Di i) _ x ℓ hxl j
    have n1 : ‖j T.det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hT0)
    have n2 : ‖j (gramE (FU.Di i) e).det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hge)
    have n3 : ‖j (IsCMField.complexConj E T.det)‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hT0))
    rw [hgdet, map_mul, map_mul, norm_mul, norm_mul, Real.log_mul (mul_ne_zero n1 n2) n3,
      Real.log_mul n1 n2] at h1
    have hc2 : ((Fintype.card (Fin D.p ⊕ Fin D.q) : ℕ) : ℝ) = (D.p : ℝ) + D.q := by simp
    rw [hc2] at h1
    linarith
  · intro hel j
    rw [GlobalTheory.T.padic_norm_transition_det_one E H (FU.Di i) _ x e T ℓ hxl hel hT j, Real.log_one]
  · intro j t₀ hN
    obtain ⟨j', hj'⟩ := GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ_[ℓ] (IntermediateField.inclusion hkK).toRingHom j
    obtain ⟨V, hV, hVf, Tm, m'', δ, δ', v', w', hval, hδ, hδ', hlogδ, hlogδ', hA, hB, hfr', hiv, hiw⟩ :=
      GlobalTheory.T.cm_pack_pure_norm E H D l Xo c g ty FU i Z P hP X x hx τ ℓ j' v w hty hrt hxl hfr
    obtain ⟨hF, hφ⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt
      hmem hline he hconst hxl.1 hT hfr
    have hF' : IsFramed U τ X.β X.y v' w' := ⟨hfr'.1, hF.2.1, hfr'.2.2⟩
    have hβ : j'.comp X.β = j.comp (IntermediateField.inclusion hc).toRingHom := by
      rw [← hj']; ext a; rfl
    haveI := hV
    haveI := hVf
    have hfin := hN V X.K j' X.β X.y v' w' Tm X.t X.m m'' hval hβ hF' hiv hiw
    have hchg := hline.chg X.K X.β X.y v w v' w' (δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K))
      (δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) hF hF' hA hB
    simp only [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hchg
    have hφ0 := hline.ne X.K X.β X.y v w hF
    have hφ'0 := hline.ne X.K X.β X.y v' w' hF'
    have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
      (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    obtain ⟨hG0, hGlog⟩ := GlobalTheory.T.local_basis_gram_det_log_norm E H (FU.Di i) D.p D.q x ℓ hxl horth
    have hzt : (Z true).z ^ D.p ≠ 0 := pow_ne_zero _ (GlobalTheory.T.curve_z_ne_zero E H _ (Z true))
    have hC : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
      apply mul_right_cancel₀ hzt
      rw [hφ, ← hz]
      ring
    have hK : φ X.K X.y v w * X.β (tauE c τ T.det)
        = (IntermediateField.inclusion hkK).toRingHom r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
      Subtype.ext hC
    have hjE : j'.comp (X.β.comp (tauE c τ))
        = j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) := by
      rw [← RingHom.comp_assoc, hβ, RingHom.comp_assoc]
    have happ : ∀ a : E, j' (X.β (tauE c τ a))
        = j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) a) := fun a =>
      congrArg (fun f : E →+* ℂ_[ℓ] => f a) hjE
    have hjr : j' ((IntermediateField.inclusion hkK).toRingHom r) = j r := by
      rw [← hj']; rfl
    have nφ : ‖j' (φ X.K X.y v w)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ0)
    have nφ' : ‖j' (φ X.K X.y v' w')‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ'0)
    have nδ : ‖j' δ‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ)
    have nδ' : ‖j' δ'‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ')
    have nr : ‖j r‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hr))
    have nt : ‖j' (X.β (tauE c τ T.det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hT0)))
    have nG : ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hG0)))
    have hn : ‖j' (φ X.K X.y v w)‖ * ‖j' (X.β (tauE c τ T.det))‖
        = ‖j r‖ * ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      have h := congrArg (fun a => ‖j' a‖) hK
      simpa only [map_mul, norm_mul, hjr] using h
    have hl : Real.log ‖j' (φ X.K X.y v w)‖ + Real.log ‖j' (X.β (tauE c τ T.det))‖
        = Real.log ‖j r‖ + Real.log ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      rw [← Real.log_mul nφ nt, ← Real.log_mul nr nG, hn]
    have hm : ‖j' (φ X.K X.y v' w')‖ * ‖j' δ‖ ^ D.p = ‖j' (φ X.K X.y v w)‖ * ‖j' δ'‖ ^ D.q := by
      have h := congrArg (fun a => ‖j' a‖) hchg
      simp only [map_mul, map_pow, map_one, norm_mul, norm_pow, norm_one] at h
      linear_combination h
    have hlog : Real.log ‖j' (φ X.K X.y v' w')‖ + D.p * Real.log ‖j' δ‖
        = Real.log ‖j' (φ X.K X.y v w)‖ + D.q * Real.log ‖j' δ'‖ := by
      rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul nφ' (pow_ne_zero _ nδ),
        ← Real.log_mul nφ (pow_ne_zero _ nδ'), hm]
    have hGl := hGlog (j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)))
    rw [RingHom.comp_apply, ← happ] at hGl
    rw [hjE, happ] at hlogδ
    rw [← happ]
    linear_combination -hfin + hlog + hl + hGl + (D.q : ℝ) * hlogδ' + ((D.q : ℝ) - D.p) * hlogδ

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeightStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.frame_function_cm_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (ℓ : Nat.Primes), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → ∃ t : E, (∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ + Real.log ‖j (IsCMField.complexConj E t)‖ + Real.log ‖j (gramE (FU.Di i) e).det‖ = -((D.p : ℝ) + D.q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧ (IsLocBasis (𝓞 E) ℓ e → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ = 0) ∧ ∀ (j : k →+* ℂ_[ℓ]) (t₀ : ℝ), HasFinNorm U τ φ ℓ (j.comp (IntermediateField.inclusion hc).toRingHom) t₀ → t₀ = Real.log ‖j r‖ - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) t)‖ - D.q * logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((D.q : ℝ) - D.p) * (logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (H.rt : E))‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm | exact GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm <;> assumption)
end
end
