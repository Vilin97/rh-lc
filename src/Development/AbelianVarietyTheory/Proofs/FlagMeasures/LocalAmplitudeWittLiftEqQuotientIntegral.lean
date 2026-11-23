module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariantStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorCR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Group.Units
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuous

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem uh_mul {k r : ℕ} {a b : MatKR k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem b_eq_wT (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := uh_mul hm (C.y_mem τ)
  have hJ := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hmy
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    ⟨Formalism.L2.SG.Pf.LocJEq.ujOf' _ hJ, rfl⟩
  unfold wT
  rw [dite_eq_left hex, Formalism.L2.SG.Pf.LocJEq.wloc_eq C hB u τ]
  have hc : Formalism.MainNotions.S.umat hex.choose = C.Q τ * (m * C.y τ) * C.Qi τ := hex.choose_spec
  rw [hc]
  unfold v0Of sigB
  rw [← Formalism.L2.SG.Pf.LocJEq.sig_mul τ (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hm)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (C.y_mem τ))]
  congr 2
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * m * (C.Qi τ * C.Q τ) * C.y τ * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, (C.isT τ).1, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem isSPsiEquiv_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {W F : MatKR k r → Wp}
    {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hW : IsSPsiEquiv z ψ π W)
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) : IsSPsiEquiv z ψ π F := by
  intro h hh n hn g hg
  have hhng : h * n * g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := uh_mul (uh_mul hh.1 hn.1) hg
  rw [hF _ hhng, hF g hg, Matrix.mul_assoc (h * n) g y, hW h hh n hn (g * y) (uh_mul hg hy), map_smul,
    smul_comm s (ψ n)]

theorem continuousOn_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {W F : MatKR k r → Wp} {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hW : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) :
    ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have h1 : ContinuousOn (fun m : MatKR k r => s • W (m * y)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hW.comp (continuous_id.matrix_mul continuous_const).continuousOn fun m hm => uh_mul hm hy).const_smul s
  exact h1.congr hF

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), (locS hB u u' τ).Φ m = (1 : ℂ) • wT C u τ (m * C.y τ) :=
  fun m hm => by rw [one_smul]; exact b_eq_wT C hB u τ hm

theorem phi'_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      (locS hB u u' τ).Φ' m = sclOf hB u u' τ • wT C u' τ (m * C.y τ) :=
  fun m hm => by
    show sclOf hB u u' τ • bOf hB u' τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = _
    rw [b_eq_wT C hB u' τ hm]

theorem tie_of (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hc : ∀ u, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)))
    (he : ∀ u, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)) :
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  ⟨isSPsiEquiv_transl 1 (C.y_mem τ) (he u) (phi_eq C hB u u' τ),
    isSPsiEquiv_transl _ (C.y_mem τ) (he u') (phi'_eq C hB u u' τ),
    continuousOn_transl 1 (C.y_mem τ) (hc u) (phi_eq C hB u u' τ),
    continuousOn_transl _ (C.y_mem τ) (hc u') (phi'_eq C hB u u' τ)⟩

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

theorem locS_phi_equiv_cont : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  fun D X θ C hB u u' τ _ =>
    tie_of C hB u u' τ (fun u => Formalism.L2.SG.Pf.LocF.local_continuity_all D X θ C u τ)
      (fun u => Formalism.L2.SG.Pf.EquivPf.local_equivalence_all D X θ C u τ)

end GlobalTheory.SlocTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuousStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localRealData_functions_equivariant_continuous :
    ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
      (u u' : D.what₂.Word) (τ : D.what₂.Tau),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  GlobalTheory.SlocTie.locS_phi_equiv_cont
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotient

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotTransport

lemma jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

lemma exists_unit {n m : ℕ} (ε : Fin n → Bool) (H : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (h3 : Qᴴ * Formalism.REAL.Jm ε * Q = H)
    (y : Matrix (Fin m) (Fin m) ℂ) (hy : yᴴ * H * y = H) :
    ∃ g : Formalism.REAL.UJ ε, ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Q * y⁻¹ * Qi := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := jm_mul_self ε
  have hHi : (Qi * Formalism.REAL.Jm ε * Qiᴴ) * H = 1 := by
    have : H * (Qi * Formalism.REAL.Jm ε * Qiᴴ) = 1 := by
      rw [← h3]
      calc Qᴴ * Formalism.REAL.Jm ε * Q * (Qi * Formalism.REAL.Jm ε * Qiᴴ)
          = Qᴴ * Formalism.REAL.Jm ε * (Q * Qi) * Formalism.REAL.Jm ε * Qiᴴ := by simp only [Matrix.mul_assoc]
        _ = Qᴴ * Qiᴴ := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc Qᴴ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ, Matrix.mul_one]
        _ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    exact mul_eq_one_comm.mp this
  have hl : (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = 1 := by
    calc (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = (Qi * Formalism.REAL.Jm ε * Qiᴴ) * (yᴴ * H * y) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, hHi]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  have hyr : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y hdet
  have hyl : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hdet
  have hy' : (y⁻¹)ᴴ * H * y⁻¹ = H := by
    calc (y⁻¹)ᴴ * H * y⁻¹ = (y⁻¹)ᴴ * (yᴴ * H * y) * y⁻¹ := by rw [hy]
      _ = (y * y⁻¹)ᴴ * H * (y * y⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hyr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    ⟨Q * y⁻¹ * Qi, Q * y * Qi, by
      calc Q * y⁻¹ * Qi * (Q * y * Qi) = Q * (y⁻¹ * (Qi * Q) * y) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyl, Matrix.mul_one, h2],
     by
      calc Q * y * Qi * (Q * y⁻¹ * Qi) = Q * (y * (Qi * Q) * y⁻¹) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyr, Matrix.mul_one, h2]⟩
  have hu : u ∈ Formalism.REAL.UJ ε := by
    show Formalism.REAL.inUJ ε (Q * y⁻¹ * Qi)
    unfold Formalism.REAL.inUJ
    calc (Q * y⁻¹ * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * y⁻¹ * Qi)
        = Qiᴴ * ((y⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * y⁻¹) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [h3, hy']
      _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  exact ⟨⟨u, hu⟩, rfl⟩

end GlobalTheory.QuotTransport

namespace GlobalTheory


open GlobalTheory.QuotTransport in
theorem quotMeas_besselModel_of_quotLoc : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  intro D X θ C τ γ μ ν hμ hq f hf
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  obtain ⟨g, hg⟩ := exists_unit _ _ (C.Q τ) (C.Qi τ) h1 h2 h3 (C.y τ) (C.y_mem τ)
  have h2' : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M := by
    intro M; rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hγ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      ((γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        ((((γ⁻¹ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.one_mul]
  have hc : Continuous (fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => uMat w) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcM : ∀ {h : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}, Continuous h →
      ∀ (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ)
        (B : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ),
      Continuous (fun w => (Matrix.of.symm (A * uMat (h w) * B) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    fun hh A B => (continuous_const.matrix_mul (hc.comp hh)).matrix_mul continuous_const
  have hcβ : Continuous (fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (hcM (continuous_const_mul γ⁻¹) (C.Qi τ) (C.Q τ)).matrix_mul (continuous_const (y := (C.y τ)⁻¹))
  set φ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun w => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) w) with hφ
  set α : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)) with hα
  set β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) with hβ
  have hφm : Measurable φ := (hcM continuous_id _ _).measurable
  have hαm : Measurable α := (hcM ((continuous_const.mul continuous_id).mul continuous_const) _ _).measurable
  have hβm : Measurable β := hcβ.measurable
  have hpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))) :=
    Continuous.matrix_mul continuous_snd continuous_fst
  have hj : Measurable (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j)) :=
    hf.comp hpc.measurable
  have hA : ∀ w, φ (w * g) = β (γ * w) := by
    intro w
    show Matrix.of.symm (C.Qi τ * uMat (w * g) * C.Q τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * (γ * w)) * C.Q τ * (C.y τ)⁻¹)
    rw [inv_mul_cancel_left]
    congr 1
    simp only [uMat, Subgroup.coe_mul, Units.val_mul, hg, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hB : ∀ y z, β (y * z) = fun i j => (Matrix.of (α y) * Matrix.of (β z)) i j := by
    intro y z
    simp only [hα, hβ, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply, uMat, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc, h2', hγ]
    rfl
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ) = ∫⁻ x, ∫⁻ s,
    f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(μ.map α) ∂(ν.map β)
  rw [lintegral_map (hj.lintegral_prod_right' (ν := μ.map α)) hβm]
  calc ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ)
      = ∫⁻ w, f (φ w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_map hf hφm
    _ = ∫⁻ w, f (φ (w * g)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        (lintegral_mul_right_eq_self (fun w => f (φ w)) g).symm
    _ = ∫⁻ w, f (β (γ * w)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by simp only [hA]
    _ = ∫⁻ w, f (β w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_mul_left_eq_self (fun w => f (β w)) γ
    _ = ∫⁻ z, ∫⁻ y, f (β (y * z)) ∂μ ∂ν := hq _ (hf.comp hβm)
    _ = ∫⁻ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (β z)) i j) ∂(μ.map α) ∂ν := by
        refine lintegral_congr fun z => ?_
        have hmz : Measurable (fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
            f (fun i j => (Matrix.of s * Matrix.of (β z)) i j)) := hj.comp measurable_prodMk_left
        rw [lintegral_map hmz hαm]
        simp only [hB]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotientStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quotientMeasure_besselModel_of_local_quotient : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  first | exact @GlobalTheory.quotMeas_besselModel_of_quotLoc | exact GlobalTheory.quotMeas_besselModel_of_quotLoc | (intros; apply GlobalTheory.quotMeas_besselModel_of_quotLoc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCosetStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_point_term_and_lift_same_real_double_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → ∀ τ, ∃ a ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∃ a' ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u' τ), Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ)) = a * gamR hI C t τ * a'⁻¹ := by
  first | exact @GlobalTheory.TermCoset.dcoset | exact GlobalTheory.TermCoset.dcoset | (intros; apply GlobalTheory.TermCoset.dcoset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegral

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpLoc

theorem hsNormSq_amp_loc : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  intro D X Y hF hI C hB u u' t s hs hG hr hGap τ μ ν hμ hq hroot
  have hW : ∀ τ', GoodW D τ' u u' 1 (locW C u u' τ') := fun τ' =>
    goodW_of C u u' τ' (Formalism.L2.SG.Pf.colsTypeTr C u τ') (Formalism.L2.SG.Pf.colsTypeTr C u' τ')
      (Formalism.L2.SG.Pf.zTr C u τ') (Formalism.L2.SG.Pf.zTr C u' τ') (Formalism.L2.SG.Pf.haarTr C τ')
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u' τ (s.pt.1 (vOf X τ)) ν
  have hR2 : RMeas D (locW C u u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) 1
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ)))) := by
    obtain ⟨p, hp⟩ := hroot
    refine ⟨p, _, hp, ?_⟩
    rw [ENNReal.ofReal_one, one_smul]
    exact GlobalTheory.T.quotientMeasure_besselModel_of_local_quotient D X 1 C τ (s.pt.1 (vOf X τ)) μ ν hμ hq
  obtain ⟨a, ha, a', ha', hga⟩ := GlobalTheory.T.real_point_term_and_lift_same_real_double_coset D X Y hF hI 1 C u u' t s hs τ
  have hR4 : RMeas D (locW C u u' τ) (gamR hI C t τ) 1 (nu1 hI C t τ) := by
    have h := GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u' hW t hG hr τ
    unfold nu1
    rw [dite_eq_left h]
    exact h.choose_spec
  obtain ⟨p0, hp0⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨hΦ, hΦ', hc, hc'⟩ := GlobalTheory.T.localRealData_functions_equivariant_continuous D X 1 C hB u u' τ hGap
  have h5 := GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant D τ u u' 1 (locW C u u' τ) (locS hB u u' τ) (hW τ)
    (Nat.cast_pos.2 (D.mem u).A.T_prime.pos) (Nat.cast_pos.2 (D.mem u').A.T_prime.pos) hΦ hΦ' hc hc'
    (gamR hI C t τ) a a' p0 (nu1 hI C t τ) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ))))
    hp0 ha ha' hR4 (by rw [← hga]; exact hR2)
  rw [← h5, ← hga, e1]
  exact Formalism.L2.SG.LoopTerm.hsNormSq_smul _ _

end GlobalTheory.AmpLoc
end
end
