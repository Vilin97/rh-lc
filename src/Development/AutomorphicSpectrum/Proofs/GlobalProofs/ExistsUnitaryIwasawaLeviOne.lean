module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaAll
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasis
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangularStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracketStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlockStatement
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasisStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.flag_orthonormal_adapted_basis : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ → Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧ Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Flag.exists_flag_frame | exact GlobalTheory.CompanionTheory.Flag.exists_flag_frame | (intros; apply GlobalTheory.CompanionTheory.Flag.exists_flag_frame <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolution

section

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryAssembly

theorem exists_unitary_assemble : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum k₀ hk₀ kR hkR hkRJ
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at hk₀ hkR
  have hRC : Rᴴ * C = 0 := by
    have h := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using h
  have hJ'h : J'ᴴ = J' := by
    have h1 : J' = Rᴴ * (J * R) := by
      rw [hJR, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
    rw [h1]
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hRJ : Rᴴ * J = J' * Rᴴ := by
    have h := congrArg conjTranspose hJR
    simpa only [conjTranspose_mul, hJh, hJ'h] using h
  have c2 : Cᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCJC
  have a1 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]
  have a2 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (J * (C * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc J C X, ← Matrix.mul_assoc, c2, Matrix.zero_mul]
  have a3 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Cᴴ * (R * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  have a4 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Rᴴ * (R * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have a5 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Rᴴ * (C * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hRC, Matrix.zero_mul]
  have a6 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have a7 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), J * (R * X) = R * (J' * X) := fun X => by
    rw [← Matrix.mul_assoc, hJR, Matrix.mul_assoc]
  have a8 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), Rᴴ * (J * X) = J' * (Rᴴ * X) := fun X => by
    rw [← Matrix.mul_assoc, hRJ, Matrix.mul_assoc]
  have a9 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), k₀ * (k₀ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hk₀, Matrix.one_mul]
  have a10 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (kRᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hkR, Matrix.one_mul]
  have a11 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (J' * X) = J' * (kR * X) := fun X => by
    rw [← Matrix.mul_assoc, hkRJ, Matrix.mul_assoc]
  have hs : C * Cᴴ + J * (C * (Cᴴ * J)) + R * Rᴴ = 1 := by
    simpa only [Matrix.mul_assoc] using hsum
  refine ⟨C * k₀ * Cᴴ + J * C * k₀ * Cᴴ * J + R * kR * Rᴴ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    rw [← hs]
  all_goals
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, hkRJ, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    try abel

end GlobalTheory.CompanionTheory.UnitaryAssembly
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolutionStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.unitary_lift_commuting_involution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | exact GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | (intros; apply GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriKeeps

section

@[expose] public section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviIwa

theorem block_qr {D : ℕ} (τ : Fin D → ℕ) (hτ : Monotone τ) (h : Matrix (Fin D) (Fin D) ℂ) (hu : IsUnit h)
    (ht : h.BlockTriangular τ) : ∃ k ∈ Matrix.unitaryGroup (Fin D) ℂ, ∃ b : Matrix (Fin D) (Fin D) ℂ,
      h = k * b ∧ b.BlockTriangular id ∧ k.BlockTriangular τ ∧ kᴴ.BlockTriangular τ := by
  obtain ⟨k, hk, b, rfl, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular h hu
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hbu : IsUnit b := by
    have : kᴴ * (k * b) = b := by rw [← Matrix.mul_assoc, hk2, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk2).mul hu
  have hbτ : b.BlockTriangular τ := fun i j hij => hb (by
    by_contra hc
    exact absurd (hτ (not_lt.1 hc)) (not_le.2 hij))
  haveI : Invertible b := hbu.invertible
  have hbi : (b⁻¹).BlockTriangular τ := Matrix.blockTriangular_inv_of_blockTriangular hbτ
  have hkeq : k = (k * b) * b⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu), Matrix.mul_one]
  have hkt : k.BlockTriangular τ := hkeq ▸ ht.mul hbi
  have hkinv : kᴴ = k⁻¹ := (Matrix.inv_eq_left_inv hk2).symm
  haveI : Invertible k := (IsUnit.of_mul_eq_one _ hk1).invertible
  exact ⟨k, hk, b, rfl, hb, hkt, hkinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hkt⟩

theorem blockTri_keeps {D : ℕ} {τ : Fin D → ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.BlockTriangular τ) {i : ℕ}
    {v : Fin D → ℂ} (hv : ∀ c, i ≤ τ c → v c = 0) : ∀ c, i ≤ τ c → (M *ᵥ v) c = 0 := by
  intro c hc
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : i ≤ τ d
  · rw [hv d hd, mul_zero]
  · rw [hM (lt_of_lt_of_le (not_le.1 hd) hc), zero_mul]

theorem detOn_unitary {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, k *ᵥ y ∈ V) (h' : ∀ y ∈ V, kᴴ *ᵥ y ∈ V) :
    GlobalTheory.FlagMeas.detOn k V = 1 := by
  have e := GlobalTheory.RealInd.detOn_mul h' h
  rw [Matrix.mem_unitaryGroup_iff'.1 hk |> fun x => (show kᴴ * k = 1 from x), GlobalTheory.RealInd.detOn_one,
    GlobalTheory.LeviPolar.detOn_conjTranspose n k V h h'] at e
  have h0 := GlobalTheory.LeviPolar.detOn_nonneg k V
  nlinarith


open GlobalTheory.RealInd in
theorem iwaOn_leviOne : ∀ {n a : ℕ} (ε : Fin n → Bool) (j : Fin a → ℕ) (W : GlobalTheory.RealInd.Flag n a),
    GlobalTheory.FlagMeas.IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      PositivityTheory.Tls2.Iua.IwaOn (GlobalTheory.RealInd.mats (GlobalTheory.RealInd.leviOne ε W)) := by
  intro n a ε j W hW _
  obtain ⟨h0, hm, -, hiso⟩ := hW
  obtain ⟨D, C, τ, hC, hτ, hτa, hfl⟩ := GlobalTheory.T.flag_orthonormal_adapted_basis W h0 hm
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := PI.UpqRep.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := PI.UpqRep.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJdef
  have hlast : ∀ v, C *ᵥ v ∈ W (Fin.last a) := fun v =>
    (hfl _ _).2 ⟨v, rfl, fun c hc => absurd (hτa c) (by simpa using hc)⟩
  have hCJ : Cᴴ * J * C = 0 := by
    ext c d
    have := hiso _ (hlast (Pi.single c 1)) _ (hlast (Pi.single d 1))
    have e : star (Pi.single c (1 : ℂ)) = (Pi.single c 1 : Fin D → ℂ) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp
      · simp [hx]
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e,
      Matrix.mulVec_single_one, single_one_dotProduct] at this
    simpa using this
  obtain ⟨m, R, ε', hR, hJR, hCR, hsum⟩ := GlobalTheory.T.isotropic_hyperbolic_complement ε C hC hCJ
  obtain ⟨U₀, hU₀, hI⟩ := CompanionTheory.D.gk.admitted.iwasawa_decomposition_unitary_group m ε'
  obtain ⟨U, hU, hTri⟩ := GlobalTheory.T.unitary_extension_of_block J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum U₀ hU₀
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨hgU, hgk, hgd⟩ := GlobalTheory.LeviPolar.mem_mats_leviOne.1 hg
  have hgU' : gᴴ * J * g = J := hgU
  have keep : ∀ x : Matrix (Fin n) (Fin n) ℂ, (∀ y ∈ W (Fin.last a), x *ᵥ y ∈ W (Fin.last a)) →
      x * C = C * (Cᴴ * x * C) := fun x hx => by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨w, hw, -⟩ := (hfl _ _).1 (hx _ (hlast v))
    have e : (Cᴴ * x * C) *ᵥ v = w := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hw, ← Matrix.mulVec_mulVec, e]
  set h := Cᴴ * g * C with hh
  have hgC : g * C = C * h := keep g fun y hy => (hgk _ y hy).1
  have hgC' : gᴴ * C = C * hᴴ := by
    have := keep gᴴ fun y hy => (hgk _ y hy).2
    rw [this, hh]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  have htri : h.BlockTriangular τ := by
    intro c d hdc
    have hda : τ d + 1 < a + 1 := by have := hτa d; omega
    have h1 : C *ᵥ Pi.single d 1 ∈ W ⟨τ d + 1, hda⟩ := (hfl _ _).2 ⟨_, rfl, fun c' hc' => by
      have : c' ≠ d := by rintro rfl; simp at hc'
      simp [this]⟩
    obtain ⟨v, hv, hv0⟩ := (hfl _ _).1 ((hgk _ _ h1).1)
    have h2 : h *ᵥ Pi.single d 1 = v := by
      rw [hh, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    have h3 := congrFun h2 c
    rw [Matrix.mulVec_single_one] at h3
    simpa [hv0 c (by simpa using hdc)] using h3
  obtain ⟨hu, hgJC, hgR, hgRU⟩ := GlobalTheory.T.parabolic_stabilizer_block_unit J (Formalism.REAL.Jm ε') C R hJ hJh hC hR hJR hCR hsum g h hgU' hgC hgC'
  obtain ⟨k₀, hk₀, b, hb, hbT, hk₀T, hk₀T'⟩ := block_qr τ hτ h hu htri
  obtain ⟨kR, ⟨hkR, hkRJ⟩, sR, hsR, hgks, hsT⟩ := hI (Rᴴ * g * R) hgRU
  obtain ⟨k, hk, hkJ, hkC, hkC', hkR', hkJC⟩ := GlobalTheory.T.unitary_lift_commuting_involution J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum
    k₀ hk₀ kR hkR hkRJ
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hk01 : k₀ᴴ * k₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hk₀
  have hkR1 : kRᴴ * kR = 1 := Matrix.mem_unitaryGroup_iff'.1 hkR
  have kk : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → k *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC, ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T hv⟩
  have kk' : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → kᴴ *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ᴴ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC', ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T' hv⟩
  have hkG : k ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change kᴴ * J * k = J; rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hk2, Matrix.one_mul],
      fun i y hy => ⟨kk i y hy, kk' i y hy⟩, fun i => detOn_unitary hk _ (kk i) (kk' i)⟩
  have hkhG : kᴴ ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change (kᴴ)ᴴ * J * kᴴ = J; rw [conjTranspose_conjTranspose, hkJ, Matrix.mul_assoc, hk1, Matrix.mul_one],
      fun i y hy => ⟨kk' i y hy, by simpa using kk i y hy⟩,
      fun i => detOn_unitary (Matrix.mem_unitaryGroup_iff.2 (by simpa [star_eq_conjTranspose] using hk2)) _ (kk' i)
        (by rw [conjTranspose_conjTranspose]; exact kk i)⟩
  refine ⟨k, ⟨hkG, hk⟩, kᴴ * g, GlobalTheory.LeviPolar.mats_mul hkhG hg, by rw [← Matrix.mul_assoc, hk1, Matrix.one_mul], ?_⟩
  have hbu : IsUnit b := by
    have : k₀ᴴ * h = b := by rw [hb, ← Matrix.mul_assoc, hk01, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk01).mul hu
  haveI : Invertible b := hbu.invertible
  have hci : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbT
  have hbb : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu)
  have hhinv : (hᴴ)⁻¹ = k₀ * (b⁻¹)ᴴ := Matrix.inv_eq_right_inv (by
    rw [hb, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul,
      ← conjTranspose_mul, hbb, conjTranspose_one])
  refine hTri (kᴴ * g) b (b⁻¹)ᴴ (U₀ᴴ * sR * U₀) ?_ ?_ ?_ hbT hsT ?_
  · rw [Matrix.mul_assoc, hgC, ← Matrix.mul_assoc, hkC', Matrix.mul_assoc, hb, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · have hU1 : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, hgR, ← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc kᴴ, hkR',
      Matrix.mul_assoc R, hgks, ← Matrix.mul_assoc kRᴴ, hkR1, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₀, hU1, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hgJC, ← Matrix.mul_assoc, hkJC, Matrix.mul_assoc, hhinv, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · intro x y hxy
    have := hci (show id x < id y from hxy)
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.LeviIwa
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitaryIwasawaLeviOne

section

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

theorem exists_unitary_iwasawa_leviOne : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W),
        g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  fun {_ _ ε j W} hW hj => GlobalTheory.CompanionTheory.LeviIwa.iwaOn_leviOne ε j W hW hj

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

end
end
end
