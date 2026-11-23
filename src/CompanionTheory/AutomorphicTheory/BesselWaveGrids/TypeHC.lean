module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.StatementQr
import Formalism.RealPlaceAnalysis.StatementA
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

-- Source module: CompanionTheory.HarishChandraModules.NonemptyRepresentations.IsData

section

@[expose] public section

open MeasureTheory Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.IsDataInh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem glev_last_eq (k r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun a => h2 a (by simp)⟩, fun ⟨h1, h2⟩ => ⟨h1, fun a _ => h2 a⟩⟩

theorem haar_glev_last (k r : ℕ) : ∃ μ : Measure (Mt k r), B.IsHaarOn (Glev k r (Fin.last r)) μ := by
  rw [glev_last_eq]
  exact Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r

theorem isData_of_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (hP : IsPlace P z z' π π') (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (l0 : ℕ) :
    ∃ (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
      (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))), IsData P z z' π π' X μ L st l0 := by
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P z z' π π' hP
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P z z' π π' hP X l0
  exact ⟨X, L, st, hP, hμ, h1, h2, h3, h4, h5, h6⟩

end CompanionTheory.D.Inhab.IsDataInh
end
end
end

-- Source module: CompanionTheory.HarishChandraModules.NonemptyRepresentations.TypeHW

section

@[expose] public section

open Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.TypeHW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem prod_Icc (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => f (j + 1)) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

end CompanionTheory.D.Inhab.TypeHW
end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.BesselWaveGrids.TypeHC

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.TypeHC

section param
open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem isType_of_hc {u : ℕ → ℝ} {u₀ : Fin k → ℝ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hπ : IsHCTypeW k r z u₀ π) (hu : ∀ s : Fin k, u (s.val + 1) = u₀ s) : Q.IsType k r z π u := by
  obtain ⟨p1, pmul, punit, pcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ
  have hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π := ⟨p1, pmul⟩
  have hcont : ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) := continuousOn_clm_apply.2 pcont
  obtain ⟨g, hg, h₀⟩ := hπ
  have hirr : ∀ S : Submodule ℂ W, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS => h₀.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ (conj_mem_UW hg (by
      have := Matrix.mem_unitaryGroup_iff'.mp hx.1
      rw [Matrix.star_eq_conjTranspose] at this
      exact mem_UJset_allPos.2 this)) v hv
  obtain ⟨E, hgl, -, hE⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k W _ h₀.2.2.1
  obtain ⟨v, hv, hq⟩ := qdet_eigen h₀ E hgl hE
  have hB := isFrameOf hg
  set A := g * incl k r with hA
  set B := Aᴴ * Hpk k r with hBd
  have hd : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ x, Q.dRep π (A * Z * B) x = ∑ a, ∑ b, Z a b • E a b x := by
    intro Z hZ x
    rw [← (hE Z hZ x).deriv]
    unfold Q.dRep
    congr 1
    funext t
    rw [conj_blockW hg.1, ← exp_corner _ _ (co_mul hg.1), Matrix.mul_smul, Matrix.smul_mul]
  have hH : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Hpk_mul_self
  have hc : ∀ Y : Matrix (Fin k) (Fin k) ℂ,
      (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * (A * Y * B)ᴴ * Formalism.QuantumDeterminants.Hpk k r = A * Yᴴ * B := by
    intro Y
    rw [hH, hBd]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose, ← Matrix.mul_assoc,
      Hpk_mul_self, Matrix.one_mul]
    rfl
  have hEB : Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) = E := by
    funext a b
    refine LinearMap.ext fun x => ?_
    have hl := P.QrD.frame_lie hB a b
    show P.QrD.ecOp π _ x = _
    rw [← P.QrD.ecRep_eq hrep hcont hl.1 hl.2, unitB_eq]
    unfold Q.EcRep Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [← hA, ← hBd, hc, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, hd, hd]
    · simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
      have e : ∀ c d, ((1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - (Matrix.single a b (1 : ℂ))ᴴ)) c d +
          Complex.I * ((1 / (2 * Complex.I) : ℂ) • (Matrix.single a b (1 : ℂ) + (Matrix.single a b (1 : ℂ))ᴴ)) c d =
          Matrix.single a b (1 : ℂ) c d := by
        intro c d
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
        field_simp
        ring
      simp only [e]
      simp [Matrix.single, ite_and, ite_smul]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, ← neg_smul, add_comm]
      congr 1
      simp [Complex.conj_ofNat]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]
      congr 1
      simp
  let K : Submodule ℂ W :=
    { carrier := {x | ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((k : ℂ) - 1) / 2) x = (∏ s, (Y + (u₀ s : ℂ))) • x}
      add_mem' := fun ha hb w => by rw [map_add (f := _), ha w, hb w, smul_add]
      zero_mem' := fun w => by simp
      smul_mem' := fun s x hx w => by rw [map_smul, hx w, smul_comm] }
  have hKs : Qr.Stab (Qr.EB π (fun a => g *ᵥ bvec (bl k r a))) K := by
    rw [hEB]
    intro a b x hx w
    have := congrArg (fun T : Module.End ℂ W => T x) (Formalism.REAL.qDetCentral _ k _ hgl (w + ((k : ℂ) - 1) / 2) a b)
    simp only [Module.End.mul_apply] at this
    rw [this, hx w, map_smul]
  have hK := P.lie_stabilizer W k r z π _ hz hT ⟨hrep, hcont⟩ hB K hKs
  have hKt : K = ⊤ := (hirr K hK).resolve_left ((Submodule.ne_bot_iff K).2 ⟨v, hq, hv⟩)
  refine ⟨h₀.1, hrep, hcont, punit, hirr, fun Bs hBs w x => ?_⟩
  have hx : x ∈ K := hKt ▸ Submodule.mem_top
  have e := hx (w - ((k : ℂ) - 1) / 2)
  rw [sub_add_cancel] at e
  rw [(P.frame_general_linear W k r k z π Bs ⟨hrep, hcont⟩ hBs).2, P.QrCap.capChange hz hT ⟨hrep, hcont⟩ hBs hB, hEB, e,
    CompanionTheory.D.Inhab.TypeHW.prod_Icc]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hu]
  ring

end param

theorem exists_place : ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (μW μW' : Measure (Formalism.QuantumDeterminants.Mt P.k P.r)) (l0 : ℕ), Q.IsPlace P z z' π π' → 2 ≤ P.k → 1 ≤ l0 → l0 ≤ P.k →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z) μW → μW Set.univ = 1 →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z') μW' → μW' Set.univ = 1 →
    ∃ p : KB.Pl P Wp Wq, p.l0 = l0 ∧ p.T.base.z = z ∧ p.T.base.z' = z' ∧ p.T.base.π = π ∧ p.T.base.π' = π' ∧
      p.T.base.μW = μW ∧ p.T.base.μN = D.muN P.k P.r ∧ p.T.base.μW' = μW' ∧
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P z z' π π' μW μW' l0 hP hk hl1 hl2 hW hW1 hW' hW1'
  obtain ⟨μ, hμ⟩ := CompanionTheory.D.Inhab.IsDataInh.haar_glev_last P.k P.r
  obtain ⟨hOK, hz, hz', hT, hT', ⟨-, hr, hc, hu, -, -⟩, ⟨-, hr', hc', hu', -, -⟩⟩ := id hP
  obtain ⟨B0, e1, e2, e3, e4, -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists P.k P.r Wp Wq z z' π π' hOK.k_pos hz hz'
    (by rw [hT]; exact hOK.T_pos) (by rw [hT']; exact hOK.T'_pos) hr hr' hu hu' hc hc'
  obtain ⟨T0, -, -, -, -, hN0⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq B0
  have hmuN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset P.k P.r) (D.muN P.k P.r) := by
    have h := (hN0 0 (Nat.zero_le _)).2.2
    have h' : T0.base.μN = D.muN P.k P.r := (by simpa using h : (T0.bs 0).μN = D.muN P.k P.r)
    exact h' ▸ T0.base.haarN
  subst e1 e2 e3 e4
  let Bs : B.RealPlaceData P.k P.r Wp Wq :=
    { B0 with μW := μW, μN := D.muN P.k P.r, μW' := μW', haarW := hW, haarN := hmuN, haarW' := hW' }
  obtain ⟨T, hTb, hTN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower P.k P.r Wp Wq Bs hW1 hW1' rfl
  have hPl : Q.IsPlace P T.base.z T.base.z' T.base.π T.base.π' := by
    rw [hTb]; exact hP
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of T.base
  obtain ⟨X, L, st, hD⟩ := CompanionTheory.D.Inhab.IsDataInh.isData_of_place P _ _ _ _ hPl μ hμ l0
  obtain ⟨Θ, hI, hDD⟩ := hTL Wp Wq P T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P T.base.z T.base.z' T.base.π T.base.π' (m₀ *ᵥ ν') hPl
    f1 f2 f3
  refine ⟨⟨l0, T, ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hTN, hF, hPl, ⟨X, μ, L, st, hD, hI⟩⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hDD⟩
  · change T.base.z = B0.z; rw [hTb]
  · change T.base.z' = B0.z'; rw [hTb]
  · change T.base.π = B0.π; rw [hTb]
  · change T.base.π' = B0.π'; rw [hTb]
  · change T.base.μW = μW; rw [hTb]
  · change T.base.μN = D.muN P.k P.r; rw [hTb]
  · change T.base.μW' = μW'; rw [hTb]

end CompanionTheory.WaveGrid.TypeHC
end
end
end
