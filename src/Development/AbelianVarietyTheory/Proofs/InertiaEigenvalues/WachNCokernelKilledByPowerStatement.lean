module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatWachLetterRingCompletionOfDenseSaturatedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
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
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationImageFreeAndSpansStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationQPowerMemFrobeniusSpanStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationFrobeniusMemUpToQPower

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiSat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) y
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem φD_map_Q {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (y : W.DD T₂)
    (hy : y ∈ (W.N T₁).map (mapA W π)) : ∃ j : ℕ, W.Q ^ j • W.φD T₂ y ∈ (W.N T₁).map (mapA W π) := by
  obtain ⟨n₁, hn₁, rfl⟩ := hy
  obtain ⟨j, hj⟩ := W.N_φ T₁ n₁ hn₁
  refine ⟨j, W.Q ^ j • W.φD T₁ n₁, hj, ?_⟩
  rw [map_smul]
  congr 1
  exact W.map_φ π n₁

theorem φD_satM_gen (l : ℕ) (hlp : l.Prime) (hp : PD.p = l) {T₁ T₂ : LocLat G Qp LL O}
    (π : LatHom T₁.L T₂.L) (x : W.DD T₂)
    (hx : x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) :
    ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  set N'' := (W.N T₁).map (mapA W π) with hN''
  obtain ⟨hxN, k, hk1, hk2⟩ := hx
  let J : Ideal (LetA O n) :=
    { carrier := {a | ∃ j : ℕ, W.Q ^ j • a • W.φD T₂ x ∈ N''}
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        rw [add_smul, smul_add, pow_add]
        refine N''.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N''.smul_mem _ hi
        · rw [mul_smul]; exact N''.smul_mem _ hj
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨j, hj⟩
        refine ⟨j, ?_⟩
        rw [smul_eq_mul, mul_smul, smul_comm]
        exact N''.smul_mem c hj }
  have hJ : ∀ (a : LetA O n) (j : ℕ), W.Q ^ j • a • W.φD T₂ x ∈ N'' → ∀ (b : LetA O n) (E : ℕ), j ≤ E →
      W.Q ^ E • (b * a) • W.φD T₂ x ∈ N'' := by
    intro a j hj b E hjE
    have : W.Q ^ E • (b * a) • W.φD T₂ x = (W.Q ^ (E - j) * b) • (W.Q ^ j • a • W.φD T₂ x) := by
      rw [smul_smul, smul_smul, smul_smul]
      congr 1
      conv_lhs => rw [← Nat.sub_add_cancel hjE, pow_add]
      ring
    rw [this]
    exact N''.smul_mem _ hj
  have hl : ((l : ℕ) : LetA O n) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk1
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, map_natCast] at hj
    exact hj
  have hπq : (letπ * W.q) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk2
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, W.φA_π] at hj
    exact hj
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hlp (letπ : LetA O n) 1
  have hq : letπ * W.q = (letπ + 1 : LetA O n) ^ l - 1 := by
    funext i
    have := W.q₀_def
    rw [hp] at this
    simp [letπ, LocWach.q, this, add_comm]
  have hπl : (letπ : LetA O n) ^ l = letπ * W.q - (l : LetA O n) * (letπ * r) := by
    rw [hq, hr]; ring
  have hrad : (letπ : LetA O n) ^ l ∈ J.radical := by
    rw [hπl]
    refine Ideal.sub_mem _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hπq)) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hl))
  obtain ⟨m, j₁, hj₁⟩ := hrad
  obtain ⟨j₂, hj₂⟩ := hl
  obtain ⟨a, ha⟩ := W.N_φ T₂ x hxN
  change W.Q ^ a • W.φD T₂ x ∈ W.N T₂ at ha
  refine ⟨a + j₁ + j₂, ?_, k + l * m, ?_, ?_⟩
  · rw [add_assoc, pow_add, mul_comm, mul_smul]
    exact (W.N T₂).smul_mem _ ha
  · have := hJ _ j₂ hj₂ ((l : LetA O n) ^ (l * m)) (a + j₁ + j₂) (by omega)
    rw [← pow_add, Nat.add_comm (l * m) k] at this
    rw [smul_comm]
    exact this
  · have := hJ _ j₁ hj₁ ((letπ : LetA O n) ^ k) (a + j₁ + j₂) (by omega)
    rw [← pow_mul, ← pow_add] at this
    rw [smul_comm]
    exact this

theorem φD_satM_Q : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _hc₁ _hc₂ x hx
  exact φD_satM_gen W l Fact.out ((D.loc l).PD_p K) π x hx

end GlobalTheory.NL.PhiSat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationFrobeniusMemUpToQPowerStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  first | exact @GlobalTheory.NL.PhiSat.φD_satM_Q | exact GlobalTheory.NL.PhiSat.φD_satM_Q | (intros; apply GlobalTheory.NL.PhiSat.φD_satM_Q <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationGammaStableAndSubOneMemPiSmul

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamSat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γ_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  have := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_π (g : W.Gam) : ∃ u u' : LetA O n, u * u' = 1 ∧ W.γA g letπ = letπ * u := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨u₀, hu₀⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hc : PowerSeries.constantCoeff u₀ = ((W.χΓ g : Oˣ) : O) := by
    rw [← h1, hu₀, PowerSeries.coeff_succ_X_mul]
    simp
  refine ⟨fun _ => u₀, fun _ => PowerSeries.invOfUnit u₀ (W.χΓ g), ?_, ?_⟩
  · funext i
    exact PowerSeries.mul_invOfUnit u₀ _ hc
  · funext i
    simp [LocWach.γA, letγ, letπ, hu₀]

theorem map_γ_mem {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) :
    ∀ y ∈ (W.N T₁).map (mapA W π), W.γ T₂ y ∈ (W.N T₁).map (mapA W π) := by
  rintro _ ⟨n₁, hn₁, rfl⟩
  refine ⟨W.γD T₁ W.gam n₁, W.N_Γ T₁ W.gam n₁ hn₁, ?_⟩
  change W.map π (W.γD T₁ W.gam n₁) = W.γD T₂ W.gam (W.map π n₁)
  exact W.map_γ π W.gam n₁

theorem pow_smul_γ_mem (T : LocLat G Qp LL O) (P : Submodule (LetA O n) (W.DD T))
    (hP : ∀ y ∈ P, W.γ T y ∈ P) (p k : ℕ) (x : W.DD T)
    (h1 : ((p : LetA O n)) ^ k • x ∈ P) (h2 : (letπ : LetA O n) ^ k • x ∈ P) :
    ((p : LetA O n)) ^ k • W.γ T x ∈ P ∧ (letπ : LetA O n) ^ k • W.γ T x ∈ P := by
  constructor
  · have := hP _ h1
    rw [γ_smul, map_pow, map_natCast] at this
    exact this
  · obtain ⟨u, u', huu, hu⟩ := γA_π W W.gam
    have := P.smul_mem (u' ^ k) (hP _ h2)
    have e : u' ^ k * (letπ * u) ^ k = letπ ^ k := by
      rw [← mul_pow, mul_left_comm, mul_comm u' u, huu, mul_one]
    rw [γ_smul, map_pow, hu, smul_smul, e] at this
    exact this

theorem gam_sat (p : ℕ) (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) :
    (∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧
    ∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)).map
        (smulA W T₂ letπ) := by
  set P := (W.N T₁).map (mapA W π) with hPdef
  have hP := map_γ_mem W π
  refine ⟨?_, ?_⟩
  · rintro x ⟨hx, k, h1, h2⟩
    exact ⟨W.N_Γ T₂ W.gam x hx, k, pow_smul_γ_mem W T₂ P hP p k x h1 h2⟩
  · rintro x ⟨hx, k, h1, h2⟩
    obtain ⟨y, hy, hxy⟩ := W.N_π T₂ W.gam x hx
    obtain ⟨n₁, hn₁, hn₁x⟩ := h1
    obtain ⟨m₁, hm₁, hnm⟩ := W.N_π T₁ W.gam n₁ hn₁
    have hγ := pow_smul_γ_mem W T₂ P hP p k x ⟨n₁, hn₁, hn₁x⟩ h2

    have hinj : ∀ z w : W.DD T₂, (letπ : LetA O n) • z = (letπ : LetA O n) • w → z = w := by
      intro z w hzw
      obtain ⟨u, hu⟩ := W.EE_π
      rw [← algebraMap_smul W.EE (letπ : LetA O n) z, ← algebraMap_smul W.EE (letπ : LetA O n) w,
        ← hu] at hzw
      have := congrArg (fun z => ((u⁻¹ : W.EEˣ) : W.EE) • z) hzw
      simpa [smul_smul] using this
    have hly : ((p : LetA O n)) ^ k • y = mapA W π m₁ := by
      apply hinj
      rw [smul_comm, ← hxy, smul_sub, ← LinearMap.map_smul, ← hnm]
      have e1 : W.γD T₂ W.gam (((p : LetA O n)) ^ k • x) = ((p : LetA O n)) ^ k • W.γD T₂ W.gam x := by
        have := γ_smul W T₂ (((p : LetA O n)) ^ k) x
        rw [map_pow, map_natCast] at this
        exact this
      rw [← e1, ← hn₁x]
      change W.γD T₂ W.gam (W.map π n₁) - W.map π n₁ = W.map π (W.γD T₁ W.gam n₁ - n₁)
      rw [map_sub, W.map_γ]
    refine ⟨y, ⟨hy, k + 1, ?_, ?_⟩, ?_⟩
    · rw [pow_succ', mul_smul, hly]
      exact P.smul_mem _ ⟨m₁, hm₁, rfl⟩
    · rw [pow_succ, mul_smul, ← hxy, smul_sub]
      exact P.sub_mem hγ.2 h2
    · change (letπ : LetA O n) • y = _
      rw [← hxy]
      rfl

end Generic

theorem wachSaturation_gamma_stable_and_sub_one_mem_pi_smul : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _ _
  exact gam_sat W l T₁ T₂ π

end GlobalTheory.NL.GamSat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationGammaStableAndSubOneMemPiSmulStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.saturation_gamma_stable_of_good : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  first | exact @GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | exact GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | (intros; apply GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPower

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CokerFin



theorem coker_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  intro D HW F Cm l _ K s LL h W E C T₀ T₁ T₂ ι π h0 h1 h2 hs
  have hP : WachCharacterisationLattice W := GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h
  have hp10 : p10 W T₂ := hP T₂ h2
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hfl : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_wachLetterRing_completion_of_dense_saturated ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) ((D.loc l).PD K).p W.EE W.EE_π
      W.EE_complete W.EE_dense W.EE_sat
  obtain ⟨hfree, hbc⟩ := GlobalTheory.T.wachSaturation_image_free_and_spans D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hs hfl
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.saturation_gamma_stable_of_good D HW F l K s LL h T₁ T₂ π h1 h2
  have hS := hp10 _ hfree hbc hg1 hg2 (GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power D HW F l K s LL h T₁ T₂ π h1 h2)
    (GlobalTheory.T.wachSaturation_Q_power_mem_frobenius_span D HW F l K s LL h T₁ T₂ π h1 h2 hfree hbc)
  obtain ⟨c, hc⟩ := GlobalTheory.NL.Coker.uniform (W.N_fg T₂) hS.ge
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩ := hc z hz
  exact ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩

end GlobalTheory.NL.CokerFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPowerStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachN_cokernel_killed_by_power : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  first | exact @GlobalTheory.NL.CokerFin.coker_killed | exact GlobalTheory.NL.CokerFin.coker_killed | (intros; apply GlobalTheory.NL.CokerFin.coker_killed <;> assumption)
end
end
