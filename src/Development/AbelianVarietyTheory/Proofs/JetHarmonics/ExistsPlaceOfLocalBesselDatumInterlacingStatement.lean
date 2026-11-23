module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsType
public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliParamMemIntAddHalf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducibleStatement

section

@[expose] public section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.hcTypeW_continuous_unitary_irreducible : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → Nontrivial Wp ∧ IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z) ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ (∀ S : Submodule ℂ Wp, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) := by
  first | exact @GlobalTheory.ThA.hcType_rep | exact GlobalTheory.ThA.hcType_rep | (intros; apply GlobalTheory.ThA.hcType_rep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompactUStatement

section

@[expose] public section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  first | exact @GlobalTheory.ThA.haarW_twoSided_of_left | exact GlobalTheory.ThA.haarW_twoSided_of_left | (intros; apply GlobalTheory.ThA.haarW_twoSided_of_left <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatum

section

@[expose] public section

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem exists_isStdOf (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hk : 1 ≤ k) (hsec : IsSection k r L.z L.z' μsec) :
    ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  obtain ⟨μG, hμG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨χ, hχs, hχsupp, hχint⟩ := P.character_exists_alt
  have h1 := GlobalTheory.T.hcTypeW_continuous_unitary_irreducible k r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  have h1' := GlobalTheory.T.hcTypeW_continuous_unitary_irreducible k r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hW := GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary k r L.z L.μW L.hz.1 L.hz.2 L.hμW.1 L.hμW.2
  have hW' := GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary k r L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2
  have hN := P.Dx2.MN.haar (k := k) r
  exact ⟨⟨L.z, L.z', L.π, L.π', μG, L.μW, D.muN k r, L.μW', μsec, χ, hk, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
    h1.2.1, h1'.2.1, h1.2.2.2.1, h1'.2.2.2.1, h1.2.2.1, h1'.2.2.1, hμG, hW, hN, hW', hsec, hχs, hχsupp, hχint⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ThA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatumStatement

section

@[expose] public section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_normalised_localBesselDatum : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k → IsSection k r L.z L.z' μsec → ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  first | exact @GlobalTheory.ThA.exists_isStdOf | exact GlobalTheory.ThA.exists_isStdOf | (intros; apply GlobalTheory.ThA.exists_isStdOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PlExists

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB GlobalTheory.ThA Finset NumberField MeasureTheory Formalism.QuantumDeterminants Matrix

namespace GlobalTheory.ThA

theorem plExists : PlExists := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs ν' m₀ l0 hl1 hl2 hk hW hW' hN hF hP

  obtain ⟨T, hz, hz', hπ, hπ', hTn⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have ez : (T.bs 0).z = Bs.z := hz
  have ez' : (T.bs 0).z' = Bs.z' := hz'
  have eπ : (T.bs 0).π = Bs.π := hπ
  have eπ' : (T.bs 0).π' = Bs.π' := hπ'

  let T' : D.LevTower P.k P.r Wp Wq :=
    { bs := fun j => Nat.rec (motive := fun j => B.RealPlaceData P.k (P.r - j) Wp Wq) Bs (fun n _ => T.bs (n + 1)) j
      z_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z_lev 0 hj
          rw [ez] at h0
          exact h0
        | succ n => exact (T.z_lev (n + 1) hj).trans ez
      z'_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z'_lev 0 hj
          rw [ez'] at h0
          exact h0
        | succ n => exact (T.z'_lev (n + 1) hj).trans ez'
      π_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π_lev 0 hj y
          rw [eπ] at h0
          exact h0
        | succ n => exact (T.π_lev (n + 1) hj y).trans (congrFun eπ _)
      π'_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π'_lev 0 hj y
          rw [eπ'] at h0
          exact h0
        | succ n => exact (T.π'_lev (n + 1) hj y).trans (congrFun eπ' _) }
  have hT'n : D.TowerNormalised T' := by
    intro j hj
    cases j with
    | zero => exact ⟨hW, hW', hN⟩
    | succ n => exact hTn (n + 1) hj

  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP
  obtain ⟨L, st, hXL, hQQ, hq, hinv, hstar, hstart⟩ :=
    Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP X l0
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k P.r Wp Wq Bs
  have hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 :=
    ⟨hP, hμ.1, hXL, hQQ, hq, hinv, hstar, hstart⟩
  obtain ⟨Θ, hΘ1, hΘ2⟩ := hTL Wp Wq P Bs X μ L st l0 hl1 hl2 hD

  obtain ⟨he1, he2, he3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts Bs ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' (m₀ *ᵥ ν') hP he1 he2 he3
  exact ⟨⟨l0, T', ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hT'n, hF, hP, ⟨X, μ, L, st, hD, hΘ1⟩⟩, rfl, rfl, rfl, rfl, hΘ2⟩

end GlobalTheory.ThA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceOfLocalBesselDatumInterlacing

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory.PlaceOfLocalBesselType

theorem isType_of_isHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hU : ∀ i : Fin k, U (i.val + 1) = u i) : Q.IsType k r z π U := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', h1, h2, h3, h4, h5, -⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  exact ⟨h1, h2, h3, h4, h5, GlobalTheory.ThA.capParam_of_isHCTypeW k r z u U Wp π hz hT hπ hU⟩

noncomputable def ext {k : ℕ} (u : Fin k → ℝ) (i : ℕ) : ℝ := if h : i - 1 < k then u ⟨i - 1, h⟩ else 0

theorem ext_succ {k : ℕ} (u : Fin k → ℝ) (i : Fin k) : ext u (i.val + 1) = u i := by
  simp [ext]

theorem add_one_le {a b c l : ℝ} (ha : ∃ m : ℤ, a = m + c) (hb : ∃ m : ℤ, b = m + c) (h1 : a < l) (h2 : l < b) :
    a + 1 ≤ b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have h : (m : ℝ) < n := by linarith
  have h' : m + 1 ≤ n := by exact_mod_cast h
  have h'' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h'
  linarith

end GlobalTheory.PlaceOfLocalBesselType

namespace GlobalTheory

open PlaceOfLocalBesselType

theorem exists_place_of_locBessel : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  intro k r L μsec lam0 hk h2 hsec hI hI'
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Bs, hBs⟩ := GlobalTheory.T.exists_normalised_localBesselDatum k r L μsec hk1 hsec
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of Bs
  have hT := isType_of_isHCTypeW k r L.z L.u (ext L.u) L.Wp L.π L.hz.1 L.hz.2 L.hπ (ext_succ L.u)
  have hT' := isType_of_isHCTypeW k r L.z' L.u' (ext L.u') L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ' (ext_succ L.u')
  have hZ := GlobalTheory.capelliParam_mem_int_add_half k r L.Wp L.z L.π _ L.hz.1 L.hz.2 hT
  have hZ' := GlobalTheory.capelliParam_mem_int_add_half k r L.Wq L.z' L.π' _ L.hz'.1 L.hz'.2 hT'
  have h1 : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨le_rfl, hk1⟩
  have hOK : (⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ : M.Par).OK := by
    refine ⟨hk1, L.hz.2, L.hz'.2, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ' i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      dsimp only at hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j + 1 < k := by omega
      have m1 : j + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have m2 : j + 1 + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      obtain ⟨a1, a2⟩ := hI.1 j hj
      obtain ⟨b1, b2⟩ := hI'.1 j hj
      rw [← ext_succ L.u] at a1 a2
      rw [← ext_succ L.u'] at b1 b2
      dsimp only at a1 a2 b1 b2
      have c1 := add_one_le (hZ _ m2) (hZ _ m1) a2 a1
      have c2 := add_one_le (hZ _ m2) (hZ' _ m1) a2 b1
      have c3 := add_one_le (hZ' _ m2) (hZ _ m1) b2 a1
      have c4 := add_one_le (hZ' _ m2) (hZ' _ m1) b2 b1
      simp only [M.Par.lo, M.Par.hi]
      rcases max_choice (ext L.u (j + 1 + 1)) (ext L.u' (j + 1 + 1)) with e | e <;>
        rcases min_choice (ext L.u (j + 1)) (ext L.u' (j + 1)) with e' | e' <;> rw [e, e'] <;> linarith
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hBs
  obtain ⟨Cb, hCb⟩ := GlobalTheory.ThA.plExists
  obtain ⟨p, -, hp, -⟩ := hCb L.Wp L.Wq ⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ Bs ν' m₀ 1 le_rfl hk1 h2
    (by rw [e5]; exact L.hμW.2) (by rw [e6]; exact L.hμW'.2) e7 hF
    (by rw [e1, e2, e3, e4]; exact ⟨hOK, L.hz.1, L.hz'.1, rfl, rfl, hT, hT'⟩)
  refine ⟨ext L.u, ext L.u', p, fun i => ⟨ext_succ _ i, ext_succ _ i⟩, ?_⟩
  rw [hp]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceOfLocalBesselDatumInterlacingStatement

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

theorem _root_.GlobalTheory.T.exists_place_of_localBesselDatum_interlacing : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  first | exact @GlobalTheory.exists_place_of_locBessel | exact GlobalTheory.exists_place_of_locBessel | (intros; apply GlobalTheory.exists_place_of_locBessel <;> assumption)
end
end
