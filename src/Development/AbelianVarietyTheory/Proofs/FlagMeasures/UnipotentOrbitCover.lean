module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConsecutiveRatioLeRpow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallFundamentalSetRealUnipotent
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPointStatement
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallFundamentalSetRealUnipotentStatement

section

@[expose] public section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.small_fundamental_set_real_unipotent : ∀ (I : AutInst) (x : I.GA) (g : ℕ) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), 1 ≤ g → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≠ ⊥ → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → hi ≤ rho * lo → hi ^ 2 ≤ rho / 4 → ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) → ∃ γ ∈ I.GFset ∩ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))), (x⁻¹ * γ * x).2 ∈ I.Kg g ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * rho / 4 ∧ ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) ∧ ∀ v, uMat (m v) * uMat (x.1 v) = uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v) := by
  first | exact @GlobalTheory.SmallFund.small_fundamental_set | exact GlobalTheory.SmallFund.small_fundamental_set | (intros; apply GlobalTheory.SmallFund.small_fundamental_set <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistableStatement

section

@[expose] public section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.canonicalFlag_exists_unique_semistable : ∀ (I : AutInst) (x : I.GA), (∃ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ) ∧ (∀ (a a' : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (j' : Fin a' → ℕ) (τ' : Fin a' → ℝ), HasType I x j τ → HasType I x j' τ' → ∃ h : a = a', (∀ i, j i = j' (Fin.cast h i)) ∧ ∀ i, τ i = τ' (Fin.cast h i)) ∧ ∀ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i : Fin a, S i.castSucc = stepLt I x (τ i) ∧ rkK (S i.castSucc) < rkK (S i.succ) ∧ largestSize (bas I) (frm I x) (S i.succ) = τ i ∧ (∀ N, S i.castSucc < N → N ≤ lamX I x → τ i ≤ sizeQ (bas I) (frm I x) N (S i.castSucc)) ∧ ∀ N, S i.castSucc ≤ N → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (S i.succ) N → N ≠ S i.succ → sizeQ (bas I) (frm I x) (S i.succ) N ≤ τ i) ∧ (1 ≤ I.n → (a = 0 ↔ 1 / 2 ≤ least I x) ∧ ∀ h : 0 < a, τ ⟨0, h⟩ = least I x) := by
  first | exact @GlobalTheory.PointFlag.flag_spec | exact GlobalTheory.PointFlag.flag_spec | (intros; apply GlobalTheory.PointFlag.flag_spec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallSizeCanonicalFlagPiecesProperties

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPieces

theorem sizesLe_stepLe (I : AutInst) (x : I.GA) {t : ℝ} (ht : 0 < t)
    (A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) : SizesLe I x (stepLe I x t) A' t := by
  intro N _ hN hne
  have hle : stepLe I x t ≤ lamX I x := GlobalTheory.PointFlag.stepLe_le I x t
  have hne0 : stepLe I x t ≠ ⊥ := by
    intro h0
    apply hne
    rw [h0] at hN ⊢
    exact le_bot_iff.mp hN.1
  exact (GlobalTheory.PointFlag.sizeQ_le I x hle hN hne).trans ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.1 hne0)

theorem perpIn_bot (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun y hy => hy.1
  · intro y hy
    apply Submodule.subset_span
    refine ⟨hy, fun s hs => ?_⟩
    rw [(Submodule.mem_bot _).mp hs]
    simp [Formalism.UG.hform]

theorem flag_pieces : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  intro I x a S τ hF
  have h35 := GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x
  have h34 := (GlobalTheory.T.canonicalFlag_exists_unique_semistable I x).2.2 a S τ hF
  have hsat : ∀ m, SatX I x (S m) := fun m => GlobalTheory.PointFlag.flag_sat hF m
  have hperpLast : perpIn I x (S (Fin.last a)) = stepLe I x 2 := by
    rw [hF.2.2.1, (h35.2.2.1 (1 / 2) (by norm_num)).2]
    norm_num
  have hle_last : ∀ i, S i ≤ S (Fin.last a) := fun i => hF.2.1.monotone (Fin.le_last i)
  have hlast_le : S (Fin.last a) ≤ stepLe I x 2 := by
    rw [hF.2.2.1]
    exact (GlobalTheory.PointFlag.stepLt_le_stepLe I x _).trans (GlobalTheory.PointFlag.stepLe_mono I x (by norm_num))
  refine ⟨fun i => ?_, ?_, ?_, fun i => ?_⟩
  · have hp := h35.2.2.2 (S i) (S i) (hsat i) (hsat i) le_rfl
    have hp' := h35.2.2.2 (S i) (S (Fin.last a)) (hsat i) (hsat _) (hle_last i)
    refine ⟨hsat i, hp.1, ?_, hp'.2.2.2.1, hp.2.1⟩
    rw [hperpLast]
    exact (hle_last i).trans hlast_le
  · rw [hF.1]
    exact GlobalTheory.FlagPieces.perpIn_bot I x
  · rw [hperpLast]
    exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (by norm_num) _
  · obtain ⟨hcs, _, hlarge, hge, hlei⟩ := h34.1 i
    obtain ⟨hτpos, _, hsucc, _⟩ := hF.2.2.2.2.1 i
    have hsuccle : S i.succ ≤ lamX I x := by
      rw [hsucc]
      exact GlobalTheory.PointFlag.stepLe_le I x _
    refine ⟨?_, hlei, ?_, ?_, hlarge.le, ?_⟩
    · intro N hlt hle
      exact hge N hlt (hle.trans hsuccle)
    · rw [hcs, hsucc, (h35.2.2.1 _ hτpos).1, (h35.2.2.1 _ hτpos).2]
      exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (inv_pos.mpr hτpos) _
    · intro h
      have hlt : S i.castSucc < S i.succ := hF.2.1 (Fin.castSucc_lt_succ ..)
      rw [h] at hlt
      exact not_lt_bot hlt
    · split_ifs with h
      · have e : (⟨(i : ℕ) + 1, h⟩ : Fin a).castSucc = i.succ := Fin.ext (by simp)
        have hn := (h34.1 ⟨(i : ℕ) + 1, h⟩).2.2.2.1
        rw [e] at hn
        intro N hlt hle
        exact hn N hlt hle
      · have hi := i.isLt
        have e : i.succ = Fin.last a := Fin.ext (by simp; omega)
        rw [e, hF.2.2.1]
        intro N hlt hle
        exact (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hlt hle

end GlobalTheory.FlagPieces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallSizeCanonicalFlagPiecesPropertiesStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smallSizeCanonicalFlag_pieces_properties : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  first | exact @GlobalTheory.FlagPieces.flag_pieces | exact GlobalTheory.FlagPieces.flag_pieces | (intros; apply GlobalTheory.FlagPieces.flag_pieces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentOrbitCover

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepCover

theorem isIsot_span (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (h : R ≤ perpIn I x R) : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  have hspan : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
      Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)) :=
    Submodule.span_mono h

  have h1 : ∀ s ∈ R, ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 :=
    fun s hs y hy => GlobalTheory.FlagIso.hform_span I x R (hspan hy) hs

  have h2 : ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      ∀ z ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
        Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    have hker : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
        LinearMap.ker (GlobalTheory.FlagIso.hR I.J y) := by
      rw [Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply,
        ← GlobalTheory.FlagIso.hform_star I.J I.J_herm s y, h1 s hs y hy, star_zero]
    have hz' := hker hz
    rwa [LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply] at hz'
  refine ⟨?_, h2⟩
  intro hbot
  apply h0
  rw [eq_bot_iff]
  intro r hr
  have hr' : r ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [hbot] at hr'
  exact (Submodule.mem_bot _).2 ((Submodule.mem_bot _).1 hr')

theorem unipotent_orbit_cover : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W : Submodule I.E (Fin I.n → I.E), I.IsIsot W ∧ ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA W → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ y ∈ omega I x W ((I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4), ((ν, 1) : I.GA) * x = γ * y * (1, k) := by
  intro I x g q hg hn hq hlt

  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  obtain ⟨hpieces, hzero⟩ := hspec a S τ hF
  obtain ⟨ha0, hτ0⟩ := hzero hn
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hlt)
    · exact h
  obtain ⟨hall, -, -, hstep⟩ := GlobalTheory.T.smallSizeCanonicalFlag_pieces_properties I x a S τ hF
  obtain ⟨-, -, hSlast, hτmono, hτ, -⟩ := hF

  obtain ⟨τ', hτ'⟩ : ∃ f : ℕ → ℝ, f = fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 := ⟨_, rfl⟩
  have hτ'lt : ∀ i (h : i < a), τ' i = τ ⟨i, h⟩ := by
    intro i h; rw [hτ']; exact dif_pos h
  have hτ'ge : ∀ i, a ≤ i → τ' i = 1 / 2 := by
    intro i h; rw [hτ']; exact dif_neg (not_lt.2 h)
  have hpos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    rcases lt_or_ge i a with h | h
    · rw [hτ'lt i h]; exact (hτ ⟨i, h⟩).1
    · rw [hτ'ge i h]; norm_num
  have hinc : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    rw [hτ'lt i hi]
    rcases lt_or_ge (i + 1) a with h | h
    · rw [hτ'lt (i + 1) h]
      exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · rw [hτ'ge (i + 1) h]; exact (hτ ⟨i, hi⟩).2.1
  have hlast : τ' a = 1 / 2 := hτ'ge a le_rfl

  have hrk : ∀ i (hi : i ≤ a), i ≤ rkK (S ⟨i, Nat.lt_succ_of_le hi⟩) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 : rkK (S (Fin.castSucc ⟨k, hk⟩)) < rkK (S (Fin.succ ⟨k, hk⟩)) :=
        ((hpieces ⟨k, hk⟩).2.1)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt h1 h2)
  obtain ⟨-, hrkR, -⟩ := GlobalTheory.FlagIso.flag_isotropic I x
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 : a ≤ rkK (S (Fin.last a)) := hrk a le_rfl
    rw [hSlast] at h1
    exact h1.trans ((hrkR v).trans (hq v))

  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hpos hinc hlast
  rw [hτ'lt 0 ha, hτ0 ha, hτ'lt b hb] at hratio hsq
  have hi_pos : 0 < τ ⟨b, hb⟩ := (hτ ⟨b, hb⟩).1
  have hlo_pos : 0 < τ' (b + 1) := hpos (b + 1) hb
  obtain ⟨-, -, -, hne, hlarge, hgeL⟩ := hstep ⟨b, hb⟩
  have hRperp : S (Fin.succ ⟨b, hb⟩) ≤ perpIn I x (S (Fin.succ ⟨b, hb⟩)) :=
    le_trans (hall _).2.2.1 (hall _).2.2.2.1
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S (Fin.succ ⟨b, hb⟩)) :=
    (hall _).1
  have hlo : ∀ N, S (Fin.succ ⟨b, hb⟩) < N → N ≤ lamX I x →
      τ' (b + 1) ≤ sizeQ (bas I) (frm I x) N (S (Fin.succ ⟨b, hb⟩)) := by
    rw [hτ']; exact hgeL
  refine ⟨Submodule.span I.E (S (Fin.succ ⟨b, hb⟩) : Set (Fin I.n → I.E)),
    isIsot_span I x _ hne hRperp, ?_⟩
  intro ν hν
  obtain ⟨γ, ⟨hγF, -⟩, hk, A, Z, hAZ, heq, hbound, hst⟩ :=
    GlobalTheory.T.small_fundamental_set_real_unipotent I x g (S (Fin.succ ⟨b, hb⟩)) (τ' (b + 1)) (τ ⟨b, hb⟩)
      ((2 * least I x) ^ ((1 : ℝ) / q)) hg hsat hne hRperp hi_pos hlarge hlo
      ((div_le_iff₀ hlo_pos).1 hratio) hsq ν hν

  obtain ⟨m, -, hm⟩ := hst 1 1
  have hm' : ∀ v, uMat (m v) * uMat (x.1 v) =
      uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
    intro v; simpa only [Complex.ofReal_one, one_smul] using hm v

  obtain ⟨-, -, -, -, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨-, ⟨K, hK⟩, -⟩ := hKg g hg
  have hkinv : ((x⁻¹ * γ * x).2)⁻¹ ∈ I.Kg g := by
    rw [← hK] at hk ⊢
    exact K.inv_mem hk
  refine ⟨γ, hγF, ((x⁻¹ * γ * x).2)⁻¹, hkinv, ((m * x.1 : I.Ginf), x.2), ?_, ?_⟩
  · refine ⟨rfl, A, Z, hAZ, hbound, fun v => ?_, hst⟩
    show uMat (m v) * uMat (x.1 v) = _
    exact hm' v
  · have key : ∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * (uMat (m v) * uMat (x.1 v)) := by
      intro v
      rw [heq v, hm' v]
      simp only [mul_assoc]
    refine Prod.ext ?_ ?_
    · show ν * x.1 = γ.1 * (m * x.1) * 1
      rw [mul_one]
      funext v
      exact Subtype.ext (Units.ext (key v))
    · show 1 * x.2 = γ.2 * x.2 * ((x⁻¹ * γ * x).2)⁻¹
      simp only [Prod.snd_mul, Prod.snd_inv]
      group

end GlobalTheory.DeepCover
end
end
