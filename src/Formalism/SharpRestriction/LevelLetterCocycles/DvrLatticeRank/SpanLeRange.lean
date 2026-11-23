module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfC
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfA
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LVSmulA

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.ModelFPf
open scoped TensorProduct

section Span

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)

def LV (K : ℕ) (x : W.DD T) : T.V ⊗[Qp] BdR :=
  open Classical in
  if h : W.Q ^ K • W.φD T x ∈ W.N T then W.levN T c ζ ⟨_, h⟩ K else 0

theorem LV_eq (K : ℕ) (x : W.DD T) (h : W.Q ^ K • W.φD T x ∈ W.N T) :
    LV W T c ζ K x = W.levN T c ζ ⟨_, h⟩ K := by
  unfold LV
  rw [dite_eq_left h]

theorem LV_add (K : ℕ) (x y : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hy : W.Q ^ K • W.φD T y ∈ W.N T) : LV W T c ζ K (x + y) = LV W T c ζ K x + LV W T c ζ K y := by
  have hxy : W.Q ^ K • W.φD T (x + y) ∈ W.N T := by
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ hx hy
  rw [LV_eq W T c ζ K _ hxy, LV_eq W T c ζ K _ hx, LV_eq W T c ζ K _ hy]
  rw [show (⟨_, hxy⟩ : ↥(W.N T)) = ⟨_, hx⟩ + ⟨_, hy⟩ from
    Subtype.ext (by simp only [map_add (f := _), smul_add, Submodule.coe_add]), map_add (f := _)]
  rfl

theorem LV_smulA (K : ℕ) (a : LetA O n) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hv : ∀ j : ℤ, j < K → W.levN T c ζ ⟨_, hx⟩ j = 0) :
    W.Q ^ K • W.φD T (a • x) ∈ W.N T ∧
      LV W T c ζ K (a • x) = PowerSeries.constantCoeff (W.lev c ζ (W.φA a)) • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (a • x) = W.φA a • (W.Q ^ K • W.φD T x) := by
    rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, smul_comm]
  have hax : W.Q ^ K • W.φD T (a • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hax, ?_⟩
  rw [LV_eq W T c ζ K _ hax, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hax⟩ : ↥(W.N T)) = W.φA a • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ K hv K 1 (by omega), Finset.sum_range_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

theorem LV_smulO (K : ℕ) (o : O) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T) :
    W.Q ^ K • W.φD T (o • x) ∈ W.N T ∧
      LV W T c ζ K (o • x) = algebraMap O LL o • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (o • x) = algebraMap O (LetA O n) o • (W.Q ^ K • W.φD T x) := by
    rw [map_smul, smul_comm, algebraMap_smul]
  have hox : W.Q ^ K • W.φD T (o • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hox, ?_⟩
  rw [LV_eq W T c ζ K _ hox, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hox⟩ : ↥(W.N T)) = algebraMap O (LetA O n) o • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  have hC : algebraMap O (PowerSeries LL) o = PowerSeries.C (algebraMap O LL o) := by
    rw [IsScalarTower.algebraMap_apply O LL (PowerSeries LL)]
    rfl
  rw [hs, levN_eq_serMul, AlgHom.commutes, hC]
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_C, if_neg hj, zero_smul]

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_val (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hc0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hc1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : W.DD T) (hxN : x ∈ W.N T) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) :
    W.levN T c ζ ⟨_, hk⟩ k = PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ k • valAt W T c ζ x := by
  classical
  have hex : ∃ k, W.Q ^ k • W.φD T x ∈ W.N T := ⟨k, hk⟩
  unfold valAt
  rw [dite_eq_left hex]
  have hk0 : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hk0m := Nat.find_spec hex
  have hv : ∀ j : ℤ, j < (Nat.find hex : ℤ) → W.levN T c ζ ⟨_, hk0m⟩ j = 0 :=
    fun j hj => ((hp4.2 c ζ τ hPt).1.1 ⟨x, hxN⟩ _ hk0m j).2 hj
  have hs : (⟨_, hk⟩ : ↥(W.N T)) = W.Q ^ (k - Nat.find hex) • (⟨_, hk0m⟩ : ↥(W.N T)) :=
    Subtype.ext (by
      show W.Q ^ k • W.φD T x = W.Q ^ (k - Nat.find hex) • W.Q ^ Nat.find hex • W.φD T x
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hk0])
  obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hB0 : PowerSeries.constantCoeff B' = PowerSeries.coeff 1 (W.lev c ζ W.Q) := by
    rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ _ hv k (k - Nat.find hex + 1) (by omega),
    Finset.sum_eq_single (k - Nat.find hex)]
  · have e1 : (k : ℤ) - ((k - Nat.find hex : ℕ) : ℤ) = (Nat.find hex : ℤ) := by
      rw [Nat.cast_sub hk0]
      ring
    have hcoef : PowerSeries.coeff (k - Nat.find hex) ((W.lev c ζ W.Q) ^ (k - Nat.find hex)) =
        PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ (k - Nat.find hex) := by
      rw [hB', mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [e1, map_pow, hcoef, smul_smul, ← pow_sub₀ _ hc1 hk0]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [map_pow, pow_vanish' _ hc0 _ j h, zero_smul]
    · rw [hv _ (by omega), smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end Span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SpanLeRange

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.ModelFPf
open scoped TensorProduct

section Span2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)

theorem N_φ' (x : W.DD T) (hx : x ∈ W.N T) : ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ W.N T :=
  W.N_φ T x hx

theorem Qpow_mono {x : W.DD T} {k K : ℕ} (hk : W.Q ^ k • W.φD T x ∈ W.N T) (hK : k ≤ K) :
    W.Q ^ K • W.φD T x ∈ W.N T := by
  rw [show K = (K - k) + k by omega, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ hk

theorem LV_zero (K : ℕ) : LV W T c ζ K 0 = 0 := by
  have h0 : W.Q ^ K • W.φD T 0 ∈ W.N T := by rw [map_zero, smul_zero]; exact Submodule.zero_mem _
  rw [LV_eq W T c ζ K _ h0]
  rw [show (⟨_, h0⟩ : ↥(W.N T)) = 0 from Subtype.ext (by simp), map_zero]
  rfl

theorem LV_sum {ι : Type} (K : ℕ) (s : Finset ι) (f : ι → W.DD T)
    (hf : ∀ i, W.Q ^ K • W.φD T (f i) ∈ W.N T) :
    W.Q ^ K • W.φD T (∑ i ∈ s, f i) ∈ W.N T ∧
      LV W T c ζ K (∑ i ∈ s, f i) = ∑ i ∈ s, LV W T c ζ K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.sum_empty, map_zero, smul_zero]; exact Submodule.zero_mem _, ?_⟩
    rw [Finset.sum_empty, Finset.sum_empty, LV_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ (hf a) ih.1, ?_⟩
    rw [LV_add W T c ζ K _ _ (hf a) ih.1, ih.2]

theorem letE_idem (d : ZMod n) : (letE d : LetA O n) * letE d = letE d := by
  funext i
  simp only [Pi.mul_apply, letE, Pi.single_apply]
  split_ifs <;> simp

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem span_le_range (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hc0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hc1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (π' : LetA O n) (hφπ : PowerSeries.constantCoeff (W.lev c ζ (W.φA π')) = 0)
    {r0 : ℕ} (b : Fin r0 → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r0 → LetA O n, x = ∑ j, a j • b j)
    {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (rep : Fin r → W.DD T)
    (hrep : ∀ k, rep k ∈ NcS W T (c - 1)) (hbrep : ∀ k, bL k = mkL W T π' c (rep k) (hrep k)) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ LinearMap.range (UniversalLiftFrames.Phi W T c ζ rep) := by
  classical
  set R := LinearMap.range (UniversalLiftFrames.Phi W T c ζ rep)
  set c1 := PowerSeries.coeff 1 (W.lev c ζ W.Q)
  have hvan : ∀ (x : W.DD T) (hx : x ∈ W.N T) (K : ℕ) (hK : W.Q ^ K • W.φD T x ∈ W.N T) (j : ℤ),
      j < K → W.levN T c ζ ⟨_, hK⟩ j = 0 :=
    fun x hx K hK j hj => ((hp4.2 c ζ τ hPt).1.1 ⟨x, hx⟩ K hK j).2 hj
  have hLV : ∀ (x : W.DD T) (hx : x ∈ W.N T) (K : ℕ) (hK : W.Q ^ K • W.φD T x ∈ W.N T),
      LV W T c ζ K x = c1 ^ K • valAt W T c ζ x := by
    intro x hx K hK
    rw [LV_eq W T c ζ K _ hK, levN_val W T c ζ hp4 hPt hc0 hc1 x hx K hK]
  have hcancel : ∀ (K : ℕ) (u : T.V ⊗[Qp] BdR), c1 ^ K • u ∈ R → u ∈ R := by
    intro K u hu
    have := Submodule.smul_mem R ((c1 ^ K)⁻¹) hu
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc1), one_smul] at this
  have hrepR : ∀ k, valAt W T c ζ (rep k) ∈ R := by
    intro k
    refine ⟨Pi.single k 1, ?_⟩
    rw [UniversalLiftFrames.Phi_apply]
    simp [Pi.single_apply]

  have hA : ∀ y (hy : y ∈ NcS W T (c - 1)), valAt W T c ζ y ∈ R := by
    intro y hy
    set p := (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype
    set o := bL.repr (mkL W T π' c y hy)
    have h2 : (∑ k, o k • bL k) = p.mkQ (∑ k, o k • (⟨rep k, hrep k⟩ : ↥(NcS W T (c - 1)))) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbrep]
      rfl
    have h3 : (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(NcS W T (c - 1))) : LcQ W T π' c) =
        Submodule.Quotient.mk (∑ k, o k • (⟨rep k, hrep k⟩ : ↥(NcS W T (c - 1)))) := by
      have := bL.sum_repr (mkL W T π' c y hy)
      rw [h2] at this
      exact this.symm
    have h4 := (Submodule.Quotient.eq p).1 h3
    rw [Submodule.mem_comap] at h4
    have hz : y - ∑ k, o k • rep k ∈ PiNS W T π' 1 := by simpa using h4
    obtain ⟨⟨y', hy'N, hy'⟩, -⟩ := (mem_PiNS W T π' 1 _).1 hz
    have hyeq : y = ∑ k, o k • rep k + π' • y' := by
      rw [pow_one] at hy'
      rw [hy']
      abel
    have hyN := ((mem_NcS W T _ y).1 hy).1
    have hrN : ∀ k, rep k ∈ W.N T := fun k => ((mem_NcS W T _ _).1 (hrep k)).1
    choose Kr hKr using fun k => N_φ' W T (rep k) (hrN k)
    obtain ⟨Ky, hKy⟩ := N_φ' W T y hyN
    obtain ⟨Kz, hKz⟩ := N_φ' W T y' hy'N
    set K := Ky + ∑ k, Kr k + Kz
    have hKk : ∀ k, W.Q ^ K • W.φD T (rep k) ∈ W.N T := fun k =>
      Qpow_mono W T (hKr k) (by
        have := Finset.single_le_sum (f := Kr) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega)
    have hKo : ∀ k, W.Q ^ K • W.φD T (o k • rep k) ∈ W.N T :=
      fun k => (LV_smulO W T c ζ K (o k) (rep k) (hKk k)).1
    have hKz' : W.Q ^ K • W.φD T y' ∈ W.N T := Qpow_mono W T hKz (by omega)
    have hKy' : W.Q ^ K • W.φD T y ∈ W.N T := Qpow_mono W T hKy (by omega)
    obtain ⟨hKπ, hLπ⟩ := LV_smulA W T c ζ K π' y' hKz' (hvan y' hy'N K hKz')
    obtain ⟨hKs, hLs⟩ := LV_sum W T c ζ K Finset.univ (fun k => o k • rep k) hKo
    apply hcancel K
    rw [← hLV y hyN K hKy']
    have e : LV W T c ζ K y = LV W T c ζ K (∑ k, o k • rep k + π' • y') := by rw [← hyeq]
    rw [e, LV_add W T c ζ K _ _ hKs hKπ, hLs, hLπ, hφπ, zero_smul, add_zero]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [(LV_smulO W T c ζ K (o k) (rep k) (hKk k)).2, hLV _ (hrN k) K (hKk k), smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hrepR k))

  rw [← (hp4.2 c ζ τ hPt).1.2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, k, hk, rfl⟩
  set d : ZMod n := c - 1
  have hx'N : (letE d : LetA O n) • (x : W.DD T) ∈ W.N T := Submodule.smul_mem _ _ x.2
  have ek : (letE c : LetA O n) • (W.Q ^ k • W.φD T x) = W.Q ^ k • W.φD T ((letE d : LetA O n) • (x : W.DD T)) := by
    rw [show d = c - 1 from rfl, φD_letE, smul_comm]
  have hk' : W.Q ^ k • W.φD T ((letE d : LetA O n) • (x : W.DD T)) ∈ W.N T := ek ▸ Submodule.smul_mem _ _ hk
  have hw : W.levN T c ζ ⟨_, hk⟩ k = W.levN T c ζ ⟨_, hk'⟩ k := by
    rw [← levN_letE W T c ζ ⟨_, hk⟩ k]
    rw [show (letE c : LetA O n) • (⟨_, hk⟩ : ↥(W.N T)) = ⟨_, hk'⟩ from
      Subtype.ext (by rw [Submodule.coe_smul]; exact ek)]
  rw [SetLike.mem_coe, hw, levN_val W T c ζ hp4 hPt hc0 hc1 _ hx'N k hk']
  refine Submodule.smul_mem _ _ ?_
  set x' := (letE d : LetA O n) • (x : W.DD T)
  obtain ⟨a, hax, -⟩ := hbu x' hx'N
  have hx'eq : x' = ∑ j, a j • ((letE d : LetA O n) • b j) := by
    have h1 : x' = (letE d : LetA O n) • x' := by
      show _ = (letE d : LetA O n) • ((letE d : LetA O n) • (x : W.DD T))
      rw [smul_smul, letE_idem]
    rw [h1, hax, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  have hebN : ∀ j, (letE d : LetA O n) • b j ∈ NcS W T (c - 1) := by
    intro j
    refine (mem_NcS W T _ _).2 ⟨Submodule.smul_mem _ _ (hbΔ j).1, fun δ hδ => ?_, ?_⟩
    · rw [γD_letE, (hbΔ j).2 δ hδ]
    · rw [smul_smul, letE_idem]
  have hebN' : ∀ j, (letE d : LetA O n) • b j ∈ W.N T := fun j => ((mem_NcS W T _ _).1 (hebN j)).1
  choose Kb hKb using fun j => N_φ' W T _ (hebN' j)
  set K := k + ∑ j, Kb j
  have hKb' : ∀ j, W.Q ^ K • W.φD T ((letE d : LetA O n) • b j) ∈ W.N T := fun j =>
    Qpow_mono W T (hKb j) (by
      have := Finset.single_le_sum (f := Kb) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega)
  have hKa : ∀ j, W.Q ^ K • W.φD T (a j • ((letE d : LetA O n) • b j)) ∈ W.N T :=
    fun j => (LV_smulA W T c ζ K (a j) _ (hKb' j) (hvan _ (hebN' j) K (hKb' j))).1
  have hKx : W.Q ^ K • W.φD T x' ∈ W.N T := Qpow_mono W T hk' (by omega)
  apply hcancel K
  rw [← hLV x' hx'N K hKx]
  have e : LV W T c ζ K x' = LV W T c ζ K (∑ j, a j • ((letE d : LetA O n) • b j)) := by
    rw [← hx'eq]
  rw [e, (LV_sum W T c ζ K Finset.univ _ hKa).2]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [(LV_smulA W T c ζ K (a j) _ (hKb' j) (hvan _ (hebN' j) K (hKb' j))).2,
    hLV _ (hebN' j) K (hKb' j)]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hA _ (hebN j)))

end Span2

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end
end
