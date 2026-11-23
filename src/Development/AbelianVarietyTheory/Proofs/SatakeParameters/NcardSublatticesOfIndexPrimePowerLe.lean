module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QBinomialSumCardQuotientSubspacesStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentityStatement
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementarySublatticesOfIndexDegreesQBinomial

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LatHecke

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] {r : ℕ}

abbrev Red (N : Submodule O (Fin r → K)) : Type := N ⧸ (maximalIdeal O • ⊤ : Submodule O N)

instance Red.instModule (N : Submodule O (Fin r → K)) : Module (ResidueField O) (Red N) :=
  inferInstanceAs (Module (O ⧸ maximalIdeal O) (Red N))

instance Red.instTower (N : Submodule O (Fin r → K)) : IsScalarTower O (ResidueField O) (Red N) := by
  refine ⟨fun a b x => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (a • residue O b) • (Submodule.Quotient.mk x : Red N) = a • (residue O b • (Submodule.Quotient.mk x : Red N))
  have h : ∀ (c : O) (y : N), residue O c • (Submodule.Quotient.mk y : Red N) = Submodule.Quotient.mk (c • y) :=
    fun c y => rfl
  have h2 : a • residue O b = residue O (a * b) := by
    rw [Algebra.smul_def]; simp [ResidueField.algebraMap_eq]
  rw [h2, h, h, mul_smul]; rfl

def pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) : Submodule O N :=
  (W.restrictScalars O).comap (Submodule.mkQ _)

theorem smul_top_le_pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) :
    (maximalIdeal O • ⊤ : Submodule O N) ≤ pull N W := by
  intro x hx
  have : Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N) x = 0 := by
    simpa using hx
  simp [pull, this]

theorem card_quot_pull (N : Submodule O (Fin r → K)) (W : Submodule (ResidueField O) (Red N)) :
    Nat.card (N ⧸ pull N W) = Nat.card (Red N ⧸ W) := by
  let f : N →ₗ[O] (Red N ⧸ W) := (W.mkQ.restrictScalars O) ∘ₗ (Submodule.mkQ _)
  have hs : Function.Surjective f :=
    (Submodule.mkQ_surjective W).comp (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker f = pull N W := by
    ext x
    simp [f, pull, LinearMap.mem_ker]
  exact Nat.card_congr
    ((Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)).toEquiv

theorem pull_injective (N : Submodule O (Fin r → K)) :
    Function.Injective (pull (O := O) N) := by
  intro W W' h
  apply Submodule.restrictScalars_injective O
  exact Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _) h

theorem exists_pull (N : Submodule O (Fin r → K)) (C : Submodule O N)
    (hC : (maximalIdeal O • ⊤ : Submodule O N) ≤ C) :
    ∃ W : Submodule (ResidueField O) (Red N), pull N W = C := by
  let W : Submodule (ResidueField O) (Red N) :=
    { carrier := ((C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N)) : Submodule O (Red N)) : Set (Red N))
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro c x hx
        obtain ⟨c, rfl⟩ := residue_surjective c
        have : residue O c • x = c • x := by
          rw [← algebraMap_smul (ResidueField O) c x]; rfl
        rw [this]
        have hx' : x ∈ C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N)) := hx
        exact (C.map (Submodule.mkQ (maximalIdeal O • ⊤ : Submodule O N))).smul_mem c hx' }
  refine ⟨W, ?_⟩
  have : W.restrictScalars O = C.map (Submodule.mkQ _) := by
    ext x; rfl
  rw [pull, this, Submodule.comap_map_mkQ, sup_eq_right.2 hC]

variable [IsFractionRing O K]

theorem map_subtype_smul_top (N : Submodule O (Fin r → K)) :
    (maximalIdeal O • ⊤ : Submodule O N).map N.subtype = maximalIdeal O • N := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]

def toLat (L : Lat O K r) (W : Submodule (ResidueField O) (Red L.1)) : Lat O K r :=
  ⟨(pull L.1 W).map L.1.subtype,
    { fg := by
        haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
        exact (IsNoetherian.noetherian (pull L.1 W)).map _
      linearIndepOn := by
        have hfg : ((pull L.1 W).map L.1.subtype).FG := by
          haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
          exact (IsNoetherian.noetherian (pull L.1 W)).map _
        exact (Submodule.IsLattice.of_fg K hfg).linearIndepOn
      span_eq_top := by
        have hle : (maximalIdeal O • L.1 : Submodule O (Fin r → K)) ≤ (pull L.1 W).map L.1.subtype := by
          rw [← map_subtype_smul_top]
          exact Submodule.map_mono (smul_top_le_pull _ _)
        rw [eq_top_iff, ← (maxMul L).2.span_eq_top]
        exact Submodule.span_mono hle }⟩

theorem toLat_injective (L : Lat O K r) : Function.Injective (toLat L) := by
  intro W W' h
  apply pull_injective L.1
  exact Submodule.map_injective_of_injective L.1.injective_subtype (congrArg Subtype.val h)

theorem card_quot_toLat [Finite (ResidueField O)] (L : Lat O K r)
    (W : Submodule (ResidueField O) (Red L.1)) :
    (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup = Nat.card (Red L.1 ⧸ W) := by
  have h1 : (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup
      = Nat.card (L.1 ⧸ (toLat L W).1.comap L.1.subtype) := rfl
  have h2 : (toLat L W).1.comap L.1.subtype = pull L.1 W :=
    Submodule.comap_map_eq_of_injective L.1.injective_subtype _
  rw [h1, h2, card_quot_pull]

theorem card_red [Finite (ResidueField O)] (L : Lat O K r) :
    Nat.card (Red L.1) = qRes O ^ r := by
  have hc : (maximalIdeal O • L.1).comap L.1.subtype = (maximalIdeal O • ⊤ : Submodule O L.1) := by
    rw [← map_subtype_smul_top]
    exact Submodule.comap_map_eq_of_injective L.1.injective_subtype _
  have h1 : (maxMul L).1.toAddSubgroup.relIndex L.1.toAddSubgroup
      = Nat.card (L.1 ⧸ (maximalIdeal O • L.1).comap L.1.subtype) := rfl
  rw [← relIndex_maxMul L, h1, hc]

theorem finite_red [Finite (ResidueField O)] (L : Lat O K r) : Finite (Red L.1) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_red]; exact (pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _).ne')

theorem finrank_red [Finite (ResidueField O)] (L : Lat O K r) :
    Module.finrank (ResidueField O) (Red L.1) = r := by
  haveI := finite_red L
  haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite
  have h := card_red L
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O)] at h
  exact Nat.pow_right_injective (two_le_qRes (O := O)) h

theorem ncard_subElem [Finite (ResidueField O)] (L : Lat O K r) (j : ℕ) :
    (subElem j L).ncard = Nat.card
      {W : Submodule (ResidueField O) (Red L.1) // Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j} := by
  haveI := finite_red L
  have hidx : ∀ W : Submodule (ResidueField O) (Red L.1),
      (toLat L W).1.toAddSubgroup.relIndex L.1.toAddSubgroup
        = qRes O ^ Module.finrank (ResidueField O) (Red L.1 ⧸ W) := by
    intro W
    haveI : Finite (Red L.1 ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
    haveI : Module.Finite (ResidueField O) (Red L.1 ⧸ W) := Module.Finite.of_finite
    rw [card_quot_toLat, Module.natCard_eq_pow_finrank (K := ResidueField O)]
    rfl
  have hle : ∀ W : Submodule (ResidueField O) (Red L.1), (toLat L W).1 ≤ L.1 := fun W =>
    Submodule.map_subtype_le _ _
  have hlow : ∀ W : Submodule (ResidueField O) (Red L.1),
      maximalIdeal O • L.1 ≤ (toLat L W).1 := fun W => by
    rw [← map_subtype_smul_top]
    exact Submodule.map_mono (smul_top_le_pull _ _)
  let f : {W : Submodule (ResidueField O) (Red L.1) //
      Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j} → subElem j L :=
    fun W => ⟨toLat L W.1, ⟨hle W.1, by rw [hidx, W.2]⟩, hlow W.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro W W' h
      exact Subtype.ext (toLat_injective L (congrArg (fun x => x.1) h))
    · rintro ⟨M, ⟨h1, h2⟩, h3⟩
      have hC : (maximalIdeal O • ⊤ : Submodule O L.1) ≤ M.1.comap L.1.subtype := by
        rw [← Submodule.map_le_iff_le_comap, map_subtype_smul_top]
        exact h3
      obtain ⟨W, hW⟩ := exists_pull L.1 _ hC
      have hM : toLat L W = M := by
        apply Subtype.ext
        change (pull L.1 W).map L.1.subtype = M.1
        rw [hW, Submodule.map_comap_subtype, inf_eq_right.2 h1]
      have hj : Module.finrank (ResidueField O) (Red L.1 ⧸ W) = j := by
        have := hidx W
        rw [hM, h2] at this
        exact (Nat.pow_right_injective (two_le_qRes (O := O)) this).symm
      exact ⟨⟨W, hj⟩, Subtype.ext hM⟩
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem subElem_degrees : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (L : Lat O K r), subIdx 0 L = {L} ∧ subElem 0 L = {L} ∧ (∀ k, r < k → subElem k L = ∅) ∧
      ∀ X : ℂ, ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) *
        ((subElem k L).ncard : ℂ) * X ^ k = ∏ i ∈ Finset.range r, (1 - (qRes O : ℂ) ^ i * X) := by
  intro O K _ _ _ _ _ _ _ r L
  refine ⟨subIdx_zero L, subElem_zero L, fun k hk => subElem_eq_empty hk L, fun X => ?_⟩
  haveI := finite_red L
  haveI : Module.Finite (ResidueField O) (Red L.1) := Module.Finite.of_finite
  have h := GlobalTheory.T.qBinomial_sum_card_quotient_subspaces (ResidueField O) (Red L.1) X
  rw [finrank_red L] at h
  simp only [ncard_subElem L]
  exact h

end GlobalTheory.LatHecke
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementarySublatticesOfIndexDegreesQBinomialStatement

section

@[expose] public section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.elementarySublatticesOfIndex_degrees_qBinomial : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (L : Lat O K r), subIdx 0 L = {L} ∧ subElem 0 L = {L} ∧ (∀ k, r < k → subElem k L = ∅) ∧ ∀ X : ℂ, ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) * X ^ k = ∏ i ∈ Finset.range r, (1 - (qRes O : ℂ) ^ i * X) := by
  first | exact @GlobalTheory.LatHecke.subElem_degrees | exact GlobalTheory.LatHecke.subElem_degrees | (intros; apply GlobalTheory.LatHecke.subElem_degrees <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NcardSublatticesOfIndexPrimePowerLe

section

@[expose] public section

noncomputable section

open GlobalTheory.LatHecke

namespace GlobalTheory.SubIdxCount

noncomputable def hc (q : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))

theorem hc_zero_right (q r : ℕ) : hc q r 0 = 1 := by
  induction r with
  | zero => simp [hc]
  | succ r ih => simp [hc, ih]

theorem hc_le (q : ℕ) (hq : 1 ≤ q) (r n : ℕ) : hc q r n ≤ (n + 1) ^ r * (q ^ (r - 1)) ^ n := by
  induction r generalizing n with
  | zero => simp only [hc]; split_ifs <;> simp
  | succ r ih =>
    simp only [hc]
    calc ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))
        ≤ ∑ k ∈ Finset.range (n + 1), (n + 1) ^ r * q ^ (r * n) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          calc hc q r k * q ^ (r * (n - k))
              ≤ ((k + 1) ^ r * (q ^ (r - 1)) ^ k) * q ^ (r * (n - k)) :=
                Nat.mul_le_mul_right _ (ih k)
            _ = (k + 1) ^ r * q ^ ((r - 1) * k + r * (n - k)) := by
                rw [← pow_mul, pow_add]; ring
            _ ≤ (n + 1) ^ r * q ^ (r * n) := by
                apply Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
                apply Nat.pow_le_pow_right hq
                have h1 : (r - 1) * k ≤ r * k := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                have h2 : r * k + r * (n - k) = r * n := by
                  rw [← Nat.mul_add, Nat.add_sub_cancel' hk']
                omega
      _ = (n + 1) ^ (r + 1) * (q ^ (r + 1 - 1)) ^ n := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.add_sub_cancel, ← pow_mul,
            pow_succ]
          ring

theorem one_sub_mul_geom (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X) * PowerSeries.mk (fun n => c ^ n) = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n),
      pow_succ]
    ring

def polP (q r : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range r, (1 - Polynomial.C ((q : ℂ) ^ i) * Polynomial.X)

theorem polP_mul_hc (q r : ℕ) :
    (polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ)) = 1 := by
  induction r with
  | zero =>
    ext n; simp [polP, hc, PowerSeries.coeff_one]
  | succ r ih =>
    have hmk : PowerSeries.mk (fun n => (hc q (r + 1) n : ℂ)) =
        PowerSeries.mk (fun n => (hc q r n : ℂ)) * PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n) := by
      ext n
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          PowerSeries.coeff j (PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)))]
      simp [hc, pow_mul]
    rw [polP, Finset.prod_range_succ, Polynomial.coe_mul, ← polP, hmk]
    calc (polP q r : PowerSeries ℂ) * ((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X :
          Polynomial ℂ) : PowerSeries ℂ) * (PowerSeries.mk (fun n => (hc q r n : ℂ)) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n))
        = ((polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          (((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)) := by ring
      _ = 1 := by
        rw [ih, one_mul]
        rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
          Polynomial.coe_X]
        exact one_sub_mul_geom ((q : ℂ) ^ r)

theorem coeff_relation (q r n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (polP q r).coeff k * (hc q r (n - k) : ℂ) = 0 := by
  have h := congrArg (PowerSeries.coeff n) (polP_mul_hc q r)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (polP q r : PowerSeries ℂ) *
      PowerSeries.coeff j (PowerSeries.mk (fun n => (hc q r n : ℂ))))] at h
  simpa [PowerSeries.coeff_one, show n ≠ 0 by omega, Polynomial.coeff_coe] using h

end GlobalTheory.SubIdxCount

namespace GlobalTheory.SubIdxCount

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]

theorem elem_coeff (r : ℕ) (L : Lat O K r) (k : ℕ) :
    (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) =
      (polP (qRes O) r).coeff k := by
  obtain ⟨-, -, hemp, hX⟩ := GlobalTheory.T.elementarySublatticesOfIndex_degrees_qBinomial O K r L
  have hQP : (∑ j ∈ Finset.range (r + 1), Polynomial.C ((-1 : ℂ) ^ j *
      (qRes O : ℂ) ^ (j * (j - 1) / 2) * ((subElem j L).ncard : ℂ)) * Polynomial.X ^ j) =
      polP (qRes O) r := by
    apply Polynomial.funext
    intro x
    rw [polP, Polynomial.eval_finsetSum, Polynomial.eval_prod]
    simpa using hX x
  rw [← hQP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · have : r < k := by simp at hk; omega
    rw [hemp k this]; simp

theorem ncard_subIdx_eq (r : ℕ) : ∀ (n : ℕ) (L : Lat O K r),
    (subIdx n L).ncard = hc (qRes O) r n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [subIdx_zero, Set.ncard_singleton, hc_zero_right]
  have hid := GlobalTheory.T.heckeOperator_alternating_series_identity O K r ℂ (fun _ => (1 : ℂ)) n L hn
  have hall : ∀ (m : ℕ) (M : Lat O K r),
      heckeAll m (fun _ => (1 : ℂ)) M = ((subIdx m M).ncard : ℂ) := by
    intro m M
    rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite m M)]
    simp
  have hterm : ∀ k ∈ Finset.range n,
      ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
        heckeElem (k + 1) (heckeAll (n - (k + 1)) (fun _ => (1 : ℂ))) L =
      (polP (qRes O) r).coeff (k + 1) * (hc (qRes O) r (n - (k + 1)) : ℂ) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hc' : heckeAll (n - (k + 1)) (fun (_ : Lat O K r) => (1 : ℂ)) =
        fun (_ : Lat O K r) => (hc (qRes O) r (n - (k + 1)) : ℂ) := by
      funext M; rw [hall, ih _ (by omega) M]
    rw [hc', heckeElem_eq_sum, Finset.sum_const, ← Set.ncard_eq_toFinset_card _
      (subElem_finite _ L), ← elem_coeff r L (k + 1), smul_eq_mul, nsmul_eq_mul]
    ring
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_range_succ'] at hid
  rw [hsum] at hid
  have hrel := coeff_relation (qRes O) r n hn
  rw [Finset.sum_range_succ'] at hrel
  have h0 := elem_coeff r L 0
  rw [subElem_zero, Set.ncard_singleton] at h0
  rw [heckeElem_zero, hall] at hid
  simp only [pow_zero, zero_mul, Nat.zero_div, Nat.cast_one, mul_one, Nat.sub_zero,
    one_smul] at hid h0
  rw [← h0, one_mul] at hrel
  have : ((subIdx n L).ncard : ℂ) = (hc (qRes O) r n : ℂ) := by
    linear_combination hid - hrel
  exact_mod_cast this

theorem ncard_subIdx_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (n : ℕ) (L : Lat O K r),
    ((subIdx n L).ncard : ℝ) ≤ ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
  intro O K _ _ _ _ _ _ _ r n L
  rw [ncard_subIdx_eq r n L]
  have h := hc_le (qRes O) (one_lt_qRes (O := O)).le r n
  exact_mod_cast h

end GlobalTheory.SubIdxCount
end
end
end
