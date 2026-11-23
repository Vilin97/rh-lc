module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormHermitianDescentStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormLatticeCompatibleStatement
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignatureStatement
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeRationalEmbedding
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealBasisFromLatticeBasisStatement
public import GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExists
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.CMFieldDegreeEqTwiceCard

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CMRank

theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro φ ψ h
    exact IsFractionRing.ringHom_ext (A := 𝓞 E) (K := E) (fun a => DFunLike.congr_fun h a)
  · intro s
    refine ⟨embOf s, ?_⟩
    ext a
    exact IsFractionRing.lift_algebraMap (intEmb_injective s) a

theorem natCard_intEmb (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

theorem cmFam_sum_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ]
    {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) :
    Function.Bijective
      (Sum.elim σ (fun τ => (starRingEnd ℂ).comp (σ τ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ)) := by
  have hconj : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext a
    simp
  obtain ⟨hinj, hiff⟩ := h
  constructor
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hinj hab)
    · exact absurd ⟨a, hab⟩ ((hiff (σ b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, hab.symm⟩ ((hiff (σ a)).1 ⟨a, rfl⟩)
    · have hab' : (starRingEnd ℂ).comp (σ a) = (starRingEnd ℂ).comp (σ b) := hab
      have : σ a = σ b := by
        rw [← hconj (σ a), hab', hconj]
      exact congrArg Sum.inr (hinj this)
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have hn : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hc
        exact hs ((hiff s).2 hc)
      obtain ⟨τ, hτ⟩ := hn
      refine ⟨Sum.inr τ, ?_⟩
      change (starRingEnd ℂ).comp (σ τ) = s
      rw [hτ, hconj]

theorem finrank_eq_two_mul_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  intro E _ _ _ Ψ _ σ h
  rw [← natCard_intEmb E, ← Nat.card_congr (Equiv.ofBijective _ (cmFam_sum_bijective h)),
    Nat.card_eq_fintype_card, Fintype.card_sum]
  omega

end GlobalTheory.CompanionTheory.Ar.Cusp.CMRank
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.CMFieldDegreeEqTwiceCardStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.CM_field_degree_eq_twice_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card | exact GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingInverseRootImaginary

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi

theorem conj_inv_mul_rt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (s : 𝓞 E →+* ℂ) (m : ℕ)
    (hm : m ≠ 0) : ∃ ε : ℝ, ε ^ 2 = 1 ∧ embOf s (((m : E) * (H.rt : E))⁻¹) =
      Complex.I * (((1 / ((m : ℝ) * Real.sqrt H.d)) * ε : ℝ) : ℂ) := by
  have hcoe : embOf s (H.rt : E) = s H.rt := IsFractionRing.lift_algebraMap (intEmb_injective s) H.rt
  have hw : (s H.rt) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg s H.rt_sq
    simpa [map_pow, map_neg, map_natCast] using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hr0 : 0 < Real.sqrt H.d := Real.sqrt_pos.2 hd
  have hrC : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hr2 : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ) := by
    have h := Real.sq_sqrt hd.le
    exact_mod_cast h
  have hfac : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
      (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) = 0 := by
    have : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
        (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) =
        (s H.rt) ^ 2 - Complex.I ^ 2 * ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 := by ring
    rw [this, hw, hr2, Complex.I_sq]; ring
  have hval : embOf s (((m : E) * (H.rt : E))⁻¹) = ((m : ℂ) * s H.rt)⁻¹ := by
    rw [map_inv₀, map_mul, map_natCast, hcoe]
  rcases mul_eq_zero.1 hfac with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    have hw' : s H.rt = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) := sub_eq_zero.1 h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]
    norm_num
  · refine ⟨1, by norm_num, ?_⟩
    have hw' : s H.rt = -(Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) := eq_neg_of_add_eq_zero_left h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingInverseRootImaginaryStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.embedding_inverse_root_imaginary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (s : 𝓞 E →+* ℂ) (m : ℕ), m ≠ 0 → ∃ ε : ℝ, ε ^ 2 = 1 ∧ embOf s (((m : E) * (H.rt : E))⁻¹) = Complex.I * (((1 / ((m : ℝ) * Real.sqrt H.d)) * ε : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeRationalEmbeddingStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.lattice_rational_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ], ∃ N : ℕ, Module.finrank ℚ E * N = Module.finrank ℤ Λ ∧ ∃ e : Λ →+ (Fin N → E), Function.Injective e ∧ (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) ∧ ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExistsStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.skew_hermitian_form_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)) (B : LinearMap.BilinForm ℚ (Fin N → E)), (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → ∃ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 ∧ (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) ∧ ∀ x y, h.toSesq (e x) (e y) ∈ integralClosure ℤ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace.exists_hermitian_of_trace | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace.exists_hermitian_of_trace | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace.exists_hermitian_of_trace <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbedding

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx

theorem zero_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by ext a b; simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem trace_zero_of_int {E : Type} [Field E] [NumberField E] (w : E)
    (hw : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * w) = 0) : w = 0 := by
  have nd := traceForm_nondegenerate ℚ E
  apply nd.1
  intro a
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ E ((n • a) * w) = 0 := hw ⟨n • a, hint⟩
  have hnq : ((n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have h2 : (n • a) * w = ((n : ℚ)) • (w * a) := by
    rw [← Int.cast_smul_eq_zsmul ℚ n a, smul_mul_assoc, mul_comm a w]
  rw [h2, map_smul, smul_eq_mul] at h1
  rw [Algebra.traceForm_apply]
  exact (mul_eq_zero.1 h1).resolve_left hnq

theorem exists_latEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (_H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (LatEmb F) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F
  have h0 : (0 : Fin n → ℂ) ∈ ballDom F.q := zero_mem_ballDom F.q
  obtain ⟨R, hR⟩ : ∃ R, R = F.R 0 := ⟨_, rfl⟩
  have := R.free
  have := R.fin
  have hform : R.form = F.form := by rw [hR]; exact F.form_eq 0
  have hrk := GlobalTheory.T.CM_field_degree_eq_twice_card E Ψ F.σ F.cm
  have hg := GlobalTheory.T.genus_eq_card_mul_signature E Ψ g j j' R.B F.σ F.cm (by rw [hR]; exact F.sig 0 h0)
  obtain ⟨N, hN, e, einj, esmul, hspan⟩ := GlobalTheory.T.lattice_rational_embedding E Λ
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hNj : N = j + j' := by
    rw [R.rank, hrk, hg] at hN
    have hc : 0 < Fintype.card Ψ := by omega
    have : Fintype.card Ψ * N = Fintype.card Ψ * (j + j') := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left hc this
  subst hNj
  have hunim : Function.Bijective F.form := hform ▸ R.unimod
  have halt : ∀ x, F.form x x = 0 := fun x => by rw [← hform]; exact R.alt x
  have hadj : ∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, F.form (a • x) y = F.form x (a' • y) := by
    rw [← hform]; exact R.adj
  obtain ⟨B, hBe, hBadj, hBskew, hBnd⟩ := GlobalTheory.T.alternating_form_hermitian_descent E Λ (j + j') e einj esmul hspan F.form halt hunim hadj
  obtain ⟨h, m, hm, hmaster, hint⟩ := GlobalTheory.T.skew_hermitian_form_exists E H Λ (j + j') e B hBadj hBskew hBnd
  have hdual := GlobalTheory.T.alternating_form_lattice_compatible E H Λ (j + j') e einj F.form hunim B hBe hBskew hBnd hspan h m hm hmaster
  have hrt : (H.rt : E) ≠ 0 := by
    intro h0
    have h1 : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E) := by rw [H.rt_sq]
    have hd : H.d ≠ 0 := H.d_prime.ne_zero
    simp [h0] at h1
    exact hd h1
  have hxi : ((m : E) * (H.rt : E))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by exact_mod_cast hm) hrt)
  choose eps heps hxieq using fun τ => GlobalTheory.T.embedding_inverse_root_imaginary E H (F.σ τ) m hm
  have hmat : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x)) := by
    intro x y
    have := hmaster 1 (e x) (e y)
    rw [one_mul, one_smul] at this
    rw [this, hBe]
  let lam : Module.Basis (Fin (2 * g)) ℤ Λ := (Module.finBasisOfFinrankEq ℤ Λ R.rank)
  obtain ⟨bas, hbas⟩ := GlobalTheory.T.real_basis_from_lattice_basis E Ψ g (j + j') F.σ F.cm hg Λ e hspan lam
  have hlat : IsLattice E e.range := by
    refine ⟨?_, ?_, ?_⟩
    · rintro a _ ⟨x, rfl⟩
      exact ⟨a • x, esmul a x⟩
    · have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (inferInstance : AddGroup.FG e.range)
    · rw [eq_top_iff]
      intro v _
      obtain ⟨k, x, hk, hx⟩ := hspan v
      have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
      have : v = (k : E)⁻¹ • e x := by
        rw [hx, Nat.cast_smul_eq_nsmul E k v |>.symm, smul_smul, inv_mul_cancel₀ hk', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hintegral : IsIntegralOn h e.range := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hint x y
  have hDI : IsDIntegral h (e.range.relIndex (dualLattice h e.range)) e.range := ⟨hlat, hintegral, hdual, le_rfl⟩
  have horth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0 := by
    intro x y
    have hsw : h.toSesq (e x) (e y) = 0 ↔ h.toSesq (e y) (e x) = 0 := by
      constructor
      · intro h1
        have h2 := h.isSymm.eq (e x) (e y)
        rw [h1] at h2
        simpa using h2.symm
      · intro h1
        have h2 := h.isSymm.eq (e y) (e x)
        rw [h1] at h2
        simpa using h2.symm
    have hfa : ∀ a : 𝓞 E, ((F.form (a • x) y : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x))) := by
      intro a
      rw [hmaster (a : E) (e x) (e y), ← hBe, esmul]
    rw [hsw]
    constructor
    · intro h1 a
      have := hfa a
      rw [h1, mul_zero, mul_zero, map_zero] at this
      exact_mod_cast this
    · intro h1
      have : ((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x) = 0 := by
        apply trace_zero_of_int
        intro a
        rw [← hfa a, h1 a]
        simp
      exact (mul_eq_zero.1 this).resolve_left hxi
  have hcpos : 0 < 1 / ((m : ℝ) * Real.sqrt H.d) := by
    have h1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have h2 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    positivity
  exact ⟨{ h := h, e := e, e_inj := einj, e_smul := esmul, Dn := _, integral := hDI, orth := horth,
           xi := ((m : E) * (H.rt : E))⁻¹, c := 1 / ((m : ℝ) * Real.sqrt H.d), c_pos := hcpos, eps := eps, eps_sq := heps,
           xi_eq := hxieq, form_eq := hmat, lam := lam, bas := bas, bas_eq := hbas }⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx
end
end
