module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
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
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusActionStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZeroStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

theorem _root_.GlobalTheory.T.maxCusp_killedCoefficient_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SSgt la c → ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0 := by
  first | exact @GlobalTheory.MaxCuspKilled.coefFn_eq_zero_of_killed | exact GlobalTheory.MaxCuspKilled.coefFn_eq_zero_of_killed | (intros; apply GlobalTheory.MaxCuspKilled.coefFn_eq_zero_of_killed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqSumRingHom

section

@[expose] public section

namespace GlobalTheory.TraceRealPartConjugateSum

open NumberField

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ => rfl

theorem sum_re_add_conj {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : E) :
    ∑ τ : ↥(ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X),
      Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) =
      (↑((Algebra.trace ℚ E : E → ℚ) x) : ℝ) := by
  classical
  set Ψ := ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X with hΨ
  have hconj : ∀ τ : E →+* ℂ,
      τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = τ x + (ComplexEmbedding.conjugate τ) x := by
    intro τ
    rw [map_add (f := _), ComplexEmbedding.conjugate_coe_eq, ReciprocityTheory.ChartRestriction.G.FD.cc,
      IsCMField.complexEmbedding_complexConj]
  have himg : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, ComplexEmbedding.involutive_conjugate E τ⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E τ]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have hsum : ∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = ∑ τ : E →+* ℂ, τ x := by
    rw [← Finset.sum_add_sum_compl Ψ (fun τ : E →+* ℂ => τ x), himg,
      Finset.sum_image (fun a _ b _ h => (ComplexEmbedding.involutive_conjugate E).injective h),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => hconj τ
  calc ∑ τ : ↥Ψ, Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))
      = Complex.re (∑ τ : ↥Ψ, (↑τ : E →+* ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := (Complex.re_sum _ _).symm
    _ = Complex.re (∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := by
      rw [Finset.sum_coe_sort Ψ (fun τ : E →+* ℂ => τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))]
    _ = _ := by
      rw [hsum, ← trace_eq_sum_ringHom x]
      simp

end GlobalTheory.TraceRealPartConjugateSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.HermExpo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem sum_re_eq_trace (X : Data E r) (x : E) :
    ∑ τ : X.Ψ, (τ.1 (x + cc x)).re = ((Algebra.trace ℚ E x : ℚ) : ℝ) := by
  first
  | exact @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | (apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj ..)

theorem kappa_ne (X : Data E r) : X.κ0 ≠ 0 := by
  have := X.ξ0_ne
  rcases X.κ0_xi with h | h <;> rw [h] <;> simpa using this

theorem exists_trace_repr (f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ) :
    ∃ c : Matrix (Fin ρ) (Fin ρ) E, ∀ β,
      f β = Algebra.trace ℚ E (∑ a, ∑ b, c a b * β a b) := by
  have h : ∀ g : E →ₗ[ℚ] ℚ, ∃ c : E, ∀ y, g y = Algebra.trace ℚ E (c * y) := by
    intro g
    refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm g, fun y => ?_⟩
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  choose c hc using fun a b : Fin ρ => h (f ∘ₗ Matrix.singleLinearMap ℚ a b)
  refine ⟨Matrix.of c, fun β => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single β]

  simp only [map_sum, Matrix.of_apply, ← hc]
  rfl

theorem exists_herm_phase (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ)
    (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (m : Fin (nZ X ρ) → ℤ) :
    ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  have hli : LinearIndependent ℚ (zBas X cu) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ, ∀ k, f (zBas X cu k) = m k := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      (Finsupp.linearCombination ℚ (zBas X cu)) (LinearMap.ker_eq_bot.2 hli)
    refine ⟨Finsupp.linearCombination ℚ (fun k => (m k : ℚ)) ∘ₗ g, fun k => ?_⟩
    have h1 := LinearMap.congr_fun hg (Finsupp.single k 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] at h1
    simp [h1]
  obtain ⟨c, hc⟩ := exists_trace_repr f
  have hκ : X.κ0 / 2 ≠ 0 := div_ne_zero (kappa_ne X) two_ne_zero
  have hκc : cc (X.κ0 / 2) = -(X.κ0 / 2) := by
    have := maxCuspsA_kappa_cc X
    unfold cc at this ⊢
    rw [map_div₀, this, map_ofNat, neg_div]
  have hcc : ∀ y : E, cc (cc y) = y := fun y => IsCMField.complexConj_apply_apply E y
  have hmul : ∀ y z : E, cc (y * z) = cc y * cc z := fun y z => map_mul _ y z
  have hadd : ∀ y z : E, cc (y + z) = cc y + cc z := fun y z => map_add _ y z
  have hsub : ∀ y z : E, cc (y - z) = cc y - cc z := fun y z => map_sub _ y z
  refine ⟨Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a)), fun a b => ?_, fun k => ?_⟩
  · simp only [Matrix.of_apply, hmul, hsub, hκc, hcc]
    ring
  · have hs := zBas_skew X cu ⟨_, hb⟩ k
    have hx : Matrix.trace ((Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a))).transpose *
        zBas X cu k) / (X.κ0 / 2) =
        (∑ a, ∑ b, c a b * zBas X cu k a b) + cc (∑ a, ∑ b, c a b * zBas X cu k a b) := by
      have h1 : cc (∑ a, ∑ b, c a b * zBas X cu k a b) =
          ∑ a, ∑ b, -(cc (c b a) * zBas X cu k a b) := by
        rw [Finset.sum_comm]
        unfold cc

        simp only [map_sum, map_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show IsCMField.complexConj E (zBas X cu k b a) = cc (zBas X cu k b a) from rfl, hs,
          mul_neg]
      rw [h1, div_eq_iff hκ, ← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    unfold phZ prE
    rw [hx, sum_re_eq_trace, ← hc, hf]
    simp

end GlobalTheory.HermExpo

theorem GlobalTheory.exists_isHermE_phZ_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k :=
  GlobalTheory.HermExpo.exists_herm_phase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoordsStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

theorem _root_.GlobalTheory.T.hermitian_matrix_realizes_cusp_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  first | exact @GlobalTheory.exists_isHermE_phZ_eq | exact GlobalTheory.exists_isHermE_phZ_eq | (intros; apply GlobalTheory.exists_isHermE_phZ_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory

namespace MaxCuspBwd

open MeasureTheory Complex GlobalTheory.TorusFourier

theorem integral_eq_zero_of_coeffs {ι : Type} [Fintype ι] {N : ℕ} {Γ : AddSubgroup (ι → ℝ)}
    {D : Set (ι → ℝ)} (hD : IsAddFundamentalDomain Γ D volume) (h0 : volume D ≠ 0)
    (h1 : volume D ≠ ⊤) (L : (ι → ℝ) →ₗ[ℝ] (Fin N → ℝ)) (g : (Fin N → ℝ) → ℂ) (hc : Continuous g)
    (hper : ∀ u (n : Fin N → ℤ), g (u + fun i => (n i : ℝ)) = g u)
    (hL : ∀ p ∈ Γ, ∀ k, ∃ z : ℤ, L p k = z) (ν : ι → ℝ)
    (hν : ∀ p ∈ Γ, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k)
    (h : ∀ m : Fin N → ℤ, (∀ s, ∑ k, (m k : ℝ) * L s k = 2 * ∑ τ, ν τ * s τ) →
      ∫ t in cube N, g t * chr (fun k => (m k : ℝ)) t = 0) :
    ((volume D).toReal : ℂ)⁻¹ *
      ∫ s in D, g (L s) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) = 0 := by
  classical
  set ν' : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ τ, (2 * ν τ) • LinearMap.proj τ with hν'd
  have hν'a : ∀ s, ν' s = 2 * ∑ τ, ν τ * s τ := fun s => by
    simp [hν'd, Finset.mul_sum, mul_assoc]
  have hf : ∀ i x, g (x + Pi.basisFun ℝ (Fin N) i) = g x := fun i x => by
    rw [← hper x (Pi.single i 1)]
    congr 2
    funext k
    by_cases hk : k = i <;> simp [hk]
  have hf₁ : ∀ l ∈ Γ, ∀ x, g (x + L l) = g x := fun l hl x => by
    choose z hz using hL l hl
    rw [← hper x z]
    congr 2
    funext k
    exact hz k
  have key := ((partialCoeff_spec_cube (Pi.basisFun ℝ (Fin N)) hD h0 h1 L hc hf hf₁).1 ν'
    (fun l hl => by rw [hν'a]; exact hν l hl)).2.2.2.2 (fun χ hχ hχL => by
      choose m hm using hχ
      have hsum : ∀ t : Fin N → ℝ, ∑ i, t i • Pi.basisFun ℝ (Fin N) i = t := fun t => by
        simpa using (Pi.basisFun ℝ (Fin N)).sum_repr t
      have hχa : ∀ t : Fin N → ℝ, χ t = ∑ k, t k * (m k : ℝ) := fun t => by
        conv_lhs => rw [← hsum t]

        simp only [map_sum, map_smul, hm, smul_eq_mul]
      have h2 := h m fun s => by
        rw [← hν'a, ← hχL, LinearMap.comp_apply, hχa]
        simp only [mul_comm]
      rw [← h2, cubeCoeff, cube, Set.pi_univ_Icc]
      simp only [hsum, eNeg, chr, hχa]
      rfl)
  have h3 := congrFun key 0
  rw [partialCoeff, coeff_eq] at h3
  simp only [zero_add, hν'a, Pi.zero_apply] at h3
  rw [← h3, Measure.real]
  congr 2
  funext s
  congr 2
  push_cast
  ring

end MaxCuspBwd


open MeasureTheory Complex in
theorem maxCusps_mem_SSgt_of_coef_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) → (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la → (∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0) → P ∈ X.SSgt la c := by
  intro E _ _ _ r ρ X hcu hbas la hchi c P hP hK
  refine ⟨hP, fun ξ hξ ν hν x hx => ?_⟩
  obtain ⟨cu, hspan⟩ := hcu ξ hξ
  obtain ⟨η, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hspan
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec (hbas cu)
  obtain ⟨L, hflow, hph, hLint⟩ := GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hξ.1
  have hη : η ≠ 0 := by
    rintro rfl
    exact hξ.2.2 (by simp)
  have hsec : X.IsSec la P := hP.1.1
  unfold Data.fj
  split_ifs with hfreq hdom
  · obtain ⟨-, hD, h0, h1⟩ := hdom.choose_spec
    simp only [hflow]
    refine MaxCuspBwd.integral_eq_zero_of_coeffs hD h0.ne' h1.ne L (fun u => P (zAct X cu u x))
      ?_ (maxCuspsA_periodic X cu hb la (hchi cu) P hsec x hx) (hLint la) ν hfreq fun m hm => ?_
    · exact hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x)
        fun t => zAct_mem_dom X cu (zBas_skew X cu (hbas cu)) t x hx
    · obtain ⟨χ, hχ, hχm⟩ := GlobalTheory.T.hermitian_matrix_realizes_cusp_coords E r ρ X cu hb m
      have hνχ : ∀ τ : X.Ψ, (τ.1 (hq χ η)).re = ν τ := fun τ => by
        classical
        have h2 := hph χ hχ (Pi.single τ 1)
        simp only [hχm] at h2
        rw [hm] at h2
        simpa [Pi.single_apply] using h2.symm
      have h3 := hK cu χ ⟨hχ, fun k => ⟨m k, hχm k⟩⟩
        ⟨η, hη, hξ.1, by simpa only [hνχ] using hν⟩ x hx
      rw [show phZ X cu χ = fun k => (m k : ℝ) from funext hχm] at h3
      exact h3
  · rfl
  · rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZeroStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

theorem _root_.GlobalTheory.T.maxCusp_mem_cuspForms_of_killedCoef_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) → (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la → (∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0) → P ∈ X.SSgt la c := by
  first | exact @GlobalTheory.maxCusps_mem_SSgt_of_coef_eq_zero | exact GlobalTheory.maxCusps_mem_SSgt_of_coef_eq_zero | (intros; apply GlobalTheory.maxCusps_mem_SSgt_of_coef_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspsIffKilledCoeffVanish

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory

theorem maxCusps_iff_killed_coeff_vanish : MaxCuspsStatement := by
  intro E _ _ _ r ρ X hspan hbas la hχ c P hP
  exact ⟨fun h => GlobalTheory.T.maxCusp_killedCoefficient_eq_zero E r ρ X hbas la hχ c P h,
    fun h => GlobalTheory.T.maxCusp_mem_cuspForms_of_killedCoef_zero E r ρ X hspan hbas la hχ c P hP h⟩

end GlobalTheory
end
end
