module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarMeasureScaling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorIntegralPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignature
public import Mathlib.Analysis.Complex.Norm
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyBoundedDenominators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinOpenSubBaseChange

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory


open Matrix NumberField in
open scoped TensorProduct Classical in
theorem _root_.GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral (K : Type) [Field K] [NumberField K]
    (d D : ℕ) (B : ℝ) (hD : 0 < D) :
    {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧
      ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  have hT : {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}.Finite := by
    have h := NumberField.Embeddings.finite_of_norm_le K ℂ ((D : ℝ) * B)
    refine (h.image fun x => x / (D : K)).subset ?_
    intro c hc
    refine ⟨(D : K) * c, ⟨hc.1, fun φ => ?_⟩, ?_⟩
    · have := mul_le_mul_of_nonneg_left (hc.2 φ) (Nat.cast_nonneg (α := ℝ) D)
      simpa [norm_mul] using this
    · have hD' : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
      field_simp
  have hF : (Set.pi Set.univ fun _ : Fin (d + 1) =>
      {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => hT
  refine Set.Finite.of_finite_image
    (f := fun P : Polynomial K => fun i : Fin (d + 1) => P.coeff i) (hF.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ i -
    exact ⟨(hP.2.2 i).1, (hP.2.2 i).2⟩
  · intro P hP Q hQ hPQ
    ext n
    by_cases hn : n ≤ d
    · exact congrFun hPQ ⟨n, Nat.lt_succ_of_le hn⟩
    · push_neg at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.2.1.trans_lt hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.2.1.trans_lt hn)]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicBoundedPolynomials

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_monic_bounded_polynomials : ∀ (K : Type) [Field K] [NumberField K] (d D : ℕ) (B : ℝ), 0 < D → {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧ ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  first | (exact @GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderEmbeddingOpenImmersion

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PadicPolys

theorem minpoly_coeff_bdd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1),
      f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ),
        ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  intro p _ G K' f' hf β
  obtain ⟨k0, hk0⟩ := GlobalTheory.AtPBd.main p G 1 K' f' one_pos hf
  set R : ℝ := (p : ℝ) ^ k0 with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  refine ⟨max (R * R) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y h hy φ k
  have hnrm : IsNrm G 1 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h := by
    show nrmG (sigG G 1) 1 _ = _
    simp [nrmG]
    rfl
  obtain ⟨hs, -, hrt, hrti⟩ := hk0 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h 1 hnrm (by simpa using hy)
  set yC : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyC
  have hint : IsIntegral G.F yC := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly G.F yC).Monic := minpoly.monic hint
  have hsn : ‖(((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)‖ ≤ R := by
    rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact hs
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hroot : ∀ μ ∈ ((minpoly G.F yC).map φ).roots, ‖μ‖ ≤ R * R := by
    intro μ hμ
    have hμ' : ((minpoly G.F yC).map φ).IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    rcases GlobalTheory.GlobEig.liesOver_or_conj G φ with hφ | hφ
    · obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G φ hφ yC μ hμ'
      rw [← hν]
      exact (hrt i ν hνr).trans (le_mul_of_one_le_left (by linarith) hR1)
    · have h2 := GlobalTheory.GlobEig.isRoot_minpoly_sh G yC φ μ hμ'
      obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G _ hφ (sh G yC) μ h2
      have h3 := GlobalTheory.GlobEig.isRoot_inv G i β (y : G.Cˣ × ℚˣ).1 (y : G.Cˣ × ℚˣ).2 y.2.1 ν hνr
      have h4 := hrti i _ h3
      rw [← hν]
      have e : ν = ν * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)⁻¹ * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) := by
        field_simp
      rw [e, norm_mul]
      exact mul_le_mul h4 hsn (norm_nonneg _) (by linarith)
  have hdeg : (minpoly G.F yC).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le yC
  rw [← Polynomial.coeff_map]
  exact Polynomial.coeff_bdd_of_roots_le φ hmon (IsAlgClosed.splits _) hdeg hroot k

end GlobalTheory.LKCx.PadicPolys
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyPadicBounded

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.minpoly_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1), f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ), ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  first | (exact @GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (exact GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (intros; apply GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianQuasiFiniteFinitePart

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.FinPolysIrr

theorem eig_norm_sq_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (y : grp G β) (a : PosV G v β) (hfix : FixL G v β y a.1) (w : InfinitePlace G.F) (μ : ℂ)
    (x : Fin G.n → ℂ) (hx : x ≠ 0) (hμ : G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ x = μ • x) :
    ‖μ‖ ^ 2 = ((((y : G.Cˣ × ℚˣ).2 : ℚ)) : ℝ) := by
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G w β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G w β y
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hsig := G.sig w
  refine GlobalTheory.eig_norm_sq_of_similitude G.n (G.gram w) (herm G w β) (toV G w β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm w) Z _ ?_ ?_ hZ hs0 ?_ ?_ μ x hx hμ
  · rcases hsig with h | h <;> omega
  · have := G.n_pos
    rcases hsig with h | h <;> omega
  · rw [Complex.ofReal_ratCast]; exact hsim
  · by_cases hw : w = v
    · subst hw
      obtain ⟨c, hc⟩ := hfix
      exact Or.inr ⟨c, a.1, hc, a.2⟩
    · left
      have h1 : sigPosH (G.gram_herm w) ≠ 1 := by
        intro h1
        have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := ha.le
        have := Fintype.card_le_one_iff.1 hcard ⟨w, h1⟩ ⟨v, hv⟩
        exact hw (congrArg Subtype.val this)
      rcases hsig with h | h
      · exact absurd h.1 h1
      · exact h.1

theorem minpoly_coeff_bdd_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (S : ℝ) : ∃ B : ℝ, ∀ (y : grp G β) (a : PosV G v β),
    FixL G v β y a.1 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S → ∀ (φ : G.F →+* ℂ) (k : ℕ),
    ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  refine ⟨max (√(max S 0)) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y a hfix hS φ k
  set γ : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hγ
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly G.F γ).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le γ
  have hbd : ∀ (w : InfinitePlace G.F) (z : ℂ), (minpoly G.F γ).eval₂ w.embedding z = 0 → ‖z‖ ≤ √(max S 0) := by
    intro w z hz
    obtain ⟨x, hx, hzx⟩ := GlobalTheory.LKCx.PolyArch.roots_eig_any p G w γ z hz
    have h2 := eig_norm_sq_of_a_one p G ha v hv β hβ hR y a hfix w z x hx hzx
    have h3 : ‖z‖ ^ 2 ≤ max S 0 := h2 ▸ le_max_of_le_left hS
    simpa using Real.abs_le_sqrt h3
  have hroots : ∀ z ∈ ((minpoly G.F γ).map φ).roots, ‖z‖ ≤ √(max S 0) := by
    intro z hz
    have hr : (minpoly G.F γ).eval₂ φ z = 0 := by
      have := (Polynomial.mem_roots'.1 hz).2
      rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [← h] at hr; exact hbd _ z hr
    · have hr' : (minpoly G.F γ).eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ z) = 0 := by
        rw [h]
        have := congrArg (starRingEnd ℂ) hr
        rw [map_zero, Polynomial.hom_eval₂] at this
        convert this using 2
      simpa using hbd _ _ hr'
  have := Polynomial.coeff_bdd_of_roots_le φ (minpoly.monic hint) (IsAlgClosed.splits _) hdeg hroots k
  rwa [Polynomial.coeff_map] at this

end GlobalTheory.LKCx.FinPolysIrr

namespace GlobalTheory.LKCx


open GlobalTheory.LKCx.FinPolysIrr in
theorem finite_minpoly_fix_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsym hR
  obtain ⟨D, hD, hDy⟩ := GlobalTheory.T.minpoly_bounded_denominators p G L f hf β x t hx
  obtain ⟨Bp, hBp⟩ := GlobalTheory.T.minpoly_padic_bounded p G K' f' hf' β
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.bounded_denominator_integral_power G.F p Bp
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support p G L f hf K' f' hf' β x t hx
  obtain ⟨B, hB⟩ := minpoly_coeff_bdd_of_a_one p G ha v hv β hsym hR S
  have hpD : 0 < p ^ m₀ * D := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hD
  refine (GlobalTheory.T.finite_monic_bounded_polynomials G.F (G.n ^ 2) (p ^ m₀ * D) B hpD).subset ?_
  rintro P ⟨y, a, rfl, hfix, hne⟩
  have h1 : f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0 := right_ne_zero_of_mul hne
  have hint : IsIntegral G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly.monic hint, ?_, fun k => ⟨?_, fun φ => hB y a.2 hfix (hS y a.1.1 a.1.2 h1 h2) φ k⟩⟩
  · rw [← G.rankC]; exact minpoly.natDegree_le _
  · have := hm₀ _ D (hDy y a.1.1 h1 k) (fun φ => hBp y a.1.2 h2 φ k)
    push_cast
    simpa [mul_assoc] using this

end GlobalTheory.LKCx
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermRealTrivialisation

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.orbital_term_real_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  first | (exact @GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (exact GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (intros; apply GlobalTheory.LKCx.finite_minpoly_fix_a_one  <;> assumption)
end
end
