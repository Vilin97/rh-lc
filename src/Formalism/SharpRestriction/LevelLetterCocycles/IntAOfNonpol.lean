module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.HorTrExists
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.CoprimeFrobeniusUniformizerPowers
import Formalism.SharpRestriction.LevelLetterCocycles.FrameInvPoly
import Formalism.SharpRestriction.LevelLetterCocycles.HorTrUnique
public import Formalism.SharpRestriction.LevelLetterCocycles.LetterPull
public import Formalism.SharpRestriction.LevelLetterCocycles.LinearIdentityHeadDifference
import Formalism.SharpRestriction.LevelLetterCocycles.SecInTransport
import Formalism.SharpRestriction.LevelLetterCocycles.SecOfP
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.SecOfPInt

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers Formalism.MainNotions.UnusedSlot80.LevC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O]

def IntA (a : ZMod n) (g : W.EE) : Prop := ∃ u ∈ W.AΔ, g = algebraMap (LetA O n) W.EE (letE a * u)

theorem secOfP_int (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (x : W.DD T)
    (hx : InFP W T c' e 1 x) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol
      (lA W ^ κ • x) f ∧ ∀ k, IntA W (c' + (e : ZMod n)) (f k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨yP, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨β₀, hβ₀, hyβ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 yP hyP
  have hbl : ∀ m, (letE c' : LetA O n) • b m = b m := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1.1 m).2
  have hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m) :=
    fun m => φD_pow_letter W T c' (b m) (hbl m) e
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  let β : Fin d → LetA O n := fun m => letE (c' + (e : ZMod n)) * β₀ m
  have hβ : ∀ m, β m ∈ W.AΔ := fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hβ₀ m)
  have hΛx : x = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
    rw [hyx, hyβ]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [β, mul_smul]
    rw [smul_comm, hφl]
  have hHc := hH hCA T hTc c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  set M : ℕ := A.M PD.p with hMdef
  let κ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  set D : LetA O n := W.π₀ * Λ ^ 2 with hDdef
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA (c' + (e : ZMod n)) e
  have hYM' : Y ^ M = D * ν := by rw [hYdef, hMdef, hYM]
  choose ρ hρ using fun m m' =>
    Formalism.MainNotions.UnusedSlot80.ArcF.frame_inv_poly hinj sol (fun k => (hb.2 k).2) M κ yy hyy zz hzz Y m m'
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  let GY : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m') * Y ^ r
  have hGY : ∀ k m', GY k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  let aa : Fin d → LetA O n := fun k => ∑ m', GY k m' * β m'
  have haa : ∀ k, aa k ∈ W.AΔ := fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hGY k m') (hβ m')
  have haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k := by
    intro k
    simp only [aa, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [β]
    linear_combination (GY k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))
  let w : Fin d → LetA O n := fun m => -(ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m')
  have hw : ∀ m, w m ∈ W.AΔ := fun m => W.AΔ.neg_mem (W.AΔ.mul_mem hν (W.AΔ.sum_mem fun m' _ =>
      W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _) (hβ m')))
  have hkey : ∀ m, lA W ^ κ * lA W ^ κ * β m - ∑ k, aa k * HY m k = D * w m := by
    intro m
    have A2 : ∑ k, aa k * HY m k = ∑ m', (∑ k, HY m k * GY k m') * β m' := by
      simp only [aa, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∀ m', (∑ k, HY m k * GY k m') * β m' =
        lA W ^ κ * lA W ^ κ * ((if m = m' then 1 else 0) * β m') +
          Y ^ M * (Polynomial.aeval Y (ρ m m') * β m') := by
      intro m'
      have := hρ m m'
      simp only [HY, GY] at this ⊢
      rw [this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
      unfold lA
      split_ifs <;> ring
    rw [A2, Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, w]
    rw [hYM']
    ring
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1 s) _
  refine ⟨κ, fun k => algebraMap (LetA O n) W.EE (aa k),
    ⟨κ, 0, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), fun k => Λ * aa k,
      fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨W.AΔ.mul_mem hΛm (haa k), by rw [map_mul]⟩, ?_⟩,
    fun k => ⟨aa k, haa k, by
      show algebraMap (LetA O n) W.EE (aa k) = _
      congr 1
      conv_rhs => rw [← mul_one (letE (c' + (e : ZMod n)) : LetA O n), haal k]⟩⟩
  have hsum : ∑ k, aa k • ((W.φD T) ^ e)
      (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    congr 1
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hfin0 : lA W ^ κ • lA W ^ κ • x - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      D • ∑ m, w m • ((W.φD T) ^ e) (b m) := by
    rw [hsum, hΛx]
    simp only [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [smul_smul]
    rw [← sub_smul, ← hkey m]
    congr 1
    ring
  have hfin : lA W ^ 0 • (lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, (Λ * aa k) • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
      D • ∑ m, (Λ * w m) • ((W.φD T) ^ e) (b m) := by
    have e2 : lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, (Λ * aa k) • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
        Λ • (lA W ^ κ • lA W ^ κ • x - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) := by
      rw [smul_sub, Finset.smul_sum]
      simp only [mul_smul]
      rw [smul_comm Λ (lA W ^ κ) (lA W ^ κ • x)]
    rw [pow_zero, one_smul, e2, hfin0, smul_comm Λ D, Finset.smul_sum]
    simp only [mul_smul]
  rw [hfin]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (W.AΔ.mul_mem hΛm (hw m)) (hb.1.1 m))

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.IntAOfNonpol

section

@[expose] public section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O]

theorem intA_inFr {a : ZMod n} {Λ : LetA O n} (hΛ : Λ ∈ W.AΔ) {g : W.EE} (h : IntA W a g) : InFr W a 1 Λ g := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨Λ * u, W.AΔ.mul_mem hΛ hu, ?_⟩
  rw [← map_mul]
  congr 1
  ring

theorem intA_add {a : ZMod n} {g g' : W.EE} (h : IntA W a g) (h' : IntA W a g') : IntA W a (g + g') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  exact ⟨u + u', W.AΔ.add_mem hu hu', by rw [← map_add (f := _), mul_add]⟩

theorem intA_neg {a : ZMod n} {g : W.EE} (h : IntA W a g) : IntA W a (-g) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨-u, W.AΔ.neg_mem hu, by rw [← map_neg, mul_neg]⟩

theorem intA_sub {a : ZMod n} {g g' : W.EE} (h : IntA W a g) (h' : IntA W a g') : IntA W a (g - g') := by
  rw [sub_eq_add_neg]; exact intA_add W h (intA_neg W h')

theorem intA_zero {a : ZMod n} : IntA W a 0 := ⟨0, W.AΔ.zero_mem, by simp⟩

theorem intA_mul {a : ZMod n} {g : W.EE} (h : IntA W a g) {c : LetA O n} (hc : c ∈ W.AΔ) :
    IntA W a (algebraMap (LetA O n) W.EE c * g) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨c * u, W.AΔ.mul_mem hc hu, by rw [← map_mul]; congr 1; ring⟩

theorem intA_omul {a : ZMod n} {g : W.EE} (h : IntA W a g) (o : O) : IntA W a (g * algebraMap O W.EE o) := by
  rw [mul_comm, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  exact intA_mul W h (W.AΔ.algebraMap_mem o)

theorem intA_sum {a : ZMod n} {ι₀ : Type} (s : Finset ι₀) (g : ι₀ → W.EE) (h : ∀ i ∈ s, IntA W a (g i)) :
    IntA W a (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intA_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact intA_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intA_lE [NeZero n] {a : ZMod n} {g : W.EE} (h : IntA W a g) (t : ℕ) : IntA W a (lE W t * g) := by
  rw [LevC.lE_eq]; exact intA_mul W h (LevC.lA_mem W t)

theorem intA_of_inFr {a : ZMod n} {N : LetA O n} (hN : N ∈ W.AΔ) {g : W.EE} (h : InFr W a N 1 g) : IntA W a g := by
  obtain ⟨u, hu, hg⟩ := h
  refine ⟨N * u, W.AΔ.mul_mem hN hu, ?_⟩
  rw [map_one, one_mul] at hg
  rw [hg, mul_assoc]

variable [NeZero n]

theorem intA_of_nonpol (hπ : W.π₀ ∈ W.AΔ) {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {g : W.EE}
    (hα : ∀ s < e, 0 ≤ α s) (h : InId W a e α g) : IntA W a g := by
  have hden : ∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat = 1 := by
    refine Finset.prod_eq_one fun s hs => ?_
    have : (-(α s)).toNat = 0 := by have := hα s (Finset.mem_range.1 hs); omega
    rw [this, pow_zero]
  unfold InId at h
  rw [hden] at h
  exact intA_of_inFr W (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hπ s) _) h

theorem polar_core [FiniteDimensional Qp LL] (C : LevC.Ctx W) (h9 : DcrisExactStrict PD LL)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (e : ℕ) (a : ZMod n)
    (hac : c' + (e : ZMod n) = a)
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hT₂ : Win W A T₂) (hWY : Win W A Y) (hses : IsSESLat (Qp := Qp) ι π)
    {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T₂ c' b sol)
    {dY : ℕ} (bY : Fin dY → W.DD Y) (solY : Fin dY → ℕ → Fin dY → LL) (hbY : IsHor W Y c' bY solY)
    (hind2 : LinearIndependent LL fun k => dv W T₂ e b (Pi.single k 1))
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (hspanY : Submodule.span LL (Set.range fun j => dv W Y e bY (Pi.single j 1)) = DcrisL PD Y.ρ (W.emb a))
    (hNY : ∀ x, InFNc W Y a 1 x → ∃ f, InNL W Y a e (abelian₂ W A a e) bY f ∧
      RepVV W Y c' e (A.M PD.p) (abelian₂ W A a e) bY solY (lA W ^ A.σ PD.p • x) f)
    (w : W.DD T₂) (p x : W.DD Y) (hw : InFP W T₂ c' e 1 (abelian₂ W A a e • w)) (hp : p ∈ Pp W Y c' e)
    (hxN : InFNc W Y a 1 x) (hpx : W.map ι w = p - x) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T₂ c' e (A.M PD.p) (abelian₂ W A a e) b sol (lA W ^ κ • w) f ∧
      SecIn W a e (LevC.condPolar (W := W) T₂ a e b) f := by
  have h2 := hT₂.1
  have hY := hWY.1
  set M : ℕ := A.M PD.p with hM
  set σ : ℕ := A.σ PD.p with hσ
  set Λ : LetA O n := abelian₂ W A a e with hΛ
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W C.hR.1 s) _

  obtain ⟨κ₁, F, hF, hFr⟩ := LevC.secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T₂ h2 b sol hb w
    (by rw [hac]; exact hw)
  rw [hac] at hF hFr

  choose mo hmo hmox hE using fun k => frame_const W C.hR ι h2 hY c' b hb.1 bY hbY.1 k
  set o : Fin d → Fin dY → O := fun k j => PowerSeries.constantCoeff (mo k j c') with ho
  have hFY := repVV_map W C ι h2 hY A hA a c' e b sol hb bY solY hbY o hE hF
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul] at hFY
  have hdv : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1) := fun k =>
    dv_map W ι h2 hY c' e b hb.1 bY hbY.1 k (mo k) (hmox k)

  obtain ⟨κp, G, hG, hGint⟩ := secOfP_int W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e Y hY bY solY hbY p
    ⟨p, hp, (one_smul _ _).symm⟩
  rw [hac] at hG hGint
  obtain ⟨fx, ⟨hfxr, κx, hSx⟩, hRx⟩ := hNY x hxN

  have R1 := LevC.repVV_lA Y c' e M Λ bY solY (W.map ι w) _ (κp + σ) κ₁ hFY
  have R2 := LevC.repVV_lA Y c' e M Λ bY solY p G (κ₁ + σ) κp hG
  have R3 := LevC.repVV_lA Y c' e M Λ bY solY x fx (κ₁ + κp) σ hRx
  rw [show κp + (κ₁ + σ) = κ₁ + (κp + σ) by omega] at R2
  rw [show σ + (κ₁ + κp) = κ₁ + (κp + σ) by omega] at R3
  have R23 := LevC.repVV_sub W C.hinj Y c' e M Λ bY solY _ _ _ _ R2 R3
  rw [← smul_sub, ← hpx] at R23
  have hfr1 : ∀ j, InFr W a 1 Λ (lE W (κp + σ) * ∑ k, F k * algebraMap O W.EE (o k j)) := fun j =>
    Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (LevC.inFr_sum W _ _ fun k _ => by
      rw [mul_comm, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      exact LevC.inFr_mulA W (hFr k) (W.AΔ.algebraMap_mem _)) _
  have hfr23 : ∀ j, InFr W a 1 Λ (lE W (κ₁ + σ) * G j - lE W (κ₁ + κp) * fx j) := fun j =>
    LevC.inFr_sub W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (intA_inFr W hΛm (hGint j)) _)
      (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfxr j) _)
  obtain ⟨t, ht⟩ := LevC.sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p Y
    (C.h3 Y hY) (C.hmod Y hY) A hA c' hc' hWY bY solY hbY e _ _ _ (by rw [hac]; exact R1) (by rw [hac]; exact R23)
    (by rw [hac]; exact hfr1) (by rw [hac]; exact hfr23)
  rw [hac] at ht
  choose u hu hue using ht
  simp only [map_one, one_mul, Pi.sub_apply] at hue
  set ε : Fin dY → W.EE := fun j => algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * u j) with hεdef
  have hε : ∀ j, IntA W a (ε j) := fun j =>
    ⟨W.π₀ * Λ * u j, W.AΔ.mul_mem (W.AΔ.mul_mem C.hR.1 hΛm) (hu j), by
      show algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * u j) = _
      congr 1
      ring⟩
  obtain ⟨I, g, cc, α, hgα, hfx⟩ := hSx

  have hpv : ∀ i, ∃ (m : ℕ) (r : Fin d → O), (∃ s < e, α i s < 0) →
      (∀ j, ∑ k, r k * o k j = ((PD.p : ℕ) : O) ^ m * cc i j) ∧
        ∀ s < e, α i s < 0 → dvO W T₂ e b r ∈ FilS W T₂ a s (-(α i s)) := by
    intro i
    by_cases hi : ∃ s < e, α i s < 0
    · obtain ⟨m, r, h⟩ := pull_vec W C.hbij h9 C.hV C.hinj T₂ Y ι π hses h2 hY a e b bY hspan2 hindY hspanY o hdv
        (α i) (cc i) (hgα i).2 hi
      exact ⟨m, r, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hi⟩
  choose mi ri hri using hpv
  set M0 : ℕ := ∑ i, mi i with hM0
  set r' : Fin I → Fin d → O := fun i k => ((PD.p : ℕ) : O) ^ (M0 - mi i) * ri i k with hr'def
  set pol : Fin I → Prop := fun i => ∃ s < e, α i s < 0 with hpol
  have hr'1 : ∀ i, pol i → ∀ j, ∑ k, r' i k * o k j = ((PD.p : ℕ) : O) ^ M0 * cc i j := by
    intro i hi j
    have hle : mi i ≤ M0 := Finset.single_le_sum (fun j _ => Nat.zero_le (mi j)) (Finset.mem_univ i)
    have h1 := (hri i hi).1 j
    calc ∑ k, r' i k * o k j = ((PD.p : ℕ) : O) ^ (M0 - mi i) * ∑ k, ri i k * o k j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by simp only [hr'def]; ring
      _ = ((PD.p : ℕ) : O) ^ M0 * cc i j := by
          rw [h1, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hr'2 : ∀ i, pol i → ∀ s < e, α i s < 0 → dvO W T₂ e b (r' i) ∈ FilS W T₂ a s (-(α i s)) := by
    intro i hi s hs hneg
    rw [show r' i = fun k => ((PD.p : ℕ) : O) ^ (M0 - mi i) * ri i k from rfl, dvO_smul]
    exact Submodule.smul_mem _ _ ((hri i hi).2 s hs hneg)

  set Spol : Fin dY → W.EE := fun j => ∑ i, if pol i then g i * algebraMap O W.EE (cc i j) else 0 with hSpol
  set Snp : Fin dY → W.EE := fun j => ∑ i, if pol i then 0 else g i * algebraMap O W.EE (cc i j) with hSnpdef
  have hsplit : ∀ j, lE W κx * fx j = Spol j + Snp j := fun j => by
    have hfxj : lE W κx * fx j = ∑ i, g i * algebraMap O W.EE (cc i j) := hfx j
    rw [hfxj, hSpol, hSnpdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hSnp : ∀ j, IntA W a (Snp j) := fun j => intA_sum W _ _ fun i _ => by
    by_cases hi : pol i
    · rw [if_pos hi]; exact intA_zero W
    · rw [if_neg hi]
      refine intA_omul W (intA_of_nonpol W C.hR.1 (fun s hs => ?_) (hgα i).1) _
      by_contra hlt
      exact hi ⟨s, hs, not_le.mp hlt⟩
  set Pv : Fin d → W.EE := fun k => ∑ i, if pol i then g i * algebraMap O W.EE (r' i k) else 0 with hPvdef
  have hPv : ∀ j, ∑ k, Pv k * algebraMap O W.EE (o k j) = lE W M0 * Spol j := fun j => by
    simp only [hPvdef, hSpol, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : pol i
    · simp only [if_pos hi]
      have h3 : ∑ k, g i * algebraMap O W.EE (r' i k) * algebraMap O W.EE (o k j) =
          g i * algebraMap O W.EE (∑ k, r' i k * o k j) := by

        rw [map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by simp only [map_mul]; ring
      rw [h3, hr'1 i hi j]
      simp only [map_mul, map_pow, map_natCast]
      unfold lE
      ring
    · simp only [if_neg hi, zero_mul, Finset.sum_const_zero, mul_zero]
  set Mt : ℕ := M0 + κx + t + κp + σ with hMt
  set Z : Fin d → W.EE := fun k => lE W Mt * F k + lE W (t + κ₁ + κp) * Pv k with hZdef
  set R : Fin dY → W.EE := fun j => lE W M0 * (lE W (κx + t + κ₁ + σ) * G j + lE W κx * ε j -
    lE W (t + κ₁ + κp) * Snp j) with hRdef
  have hZR : ∀ j, ∑ k, Z k * algebraMap O W.EE (o k j) = R j := fun j => by
    have e1 : ∑ k, Z k * algebraMap O W.EE (o k j) = lE W Mt * ∑ k, F k * algebraMap O W.EE (o k j) +
        lE W (t + κ₁ + κp) * ∑ k, Pv k * algebraMap O W.EE (o k j) := by
      simp only [hZdef, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [e1, hPv j]
    have h1 := hue j
    have h2 := hsplit j
    simp only [hRdef, hMt, lE] at h1 h2 ⊢
    linear_combination (((PD.p : ℕ) : W.EE) ^ (M0 + κx)) * h1 - (((PD.p : ℕ) : W.EE) ^ (M0 + t + κ₁ + κp)) * h2

  obtain ⟨q, D, hD⟩ := right_inv W C.hV C.hinj o
    (o_inj W C.hbij h9 T₂ Y ι π hses h2 hY a e b bY hind2 hspan2 hindY o hdv)
  have hZq : ∀ m, lE W q * Z m = ∑ j, R j * algebraMap O W.EE (D j m) := fun m => by
    have e2 : ∑ j, R j * algebraMap O W.EE (D j m) = ∑ k, Z k * algebraMap O W.EE (∑ j, o k j * D j m) := by

      simp only [← hZR, Finset.sum_mul, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by simp only [map_mul]; ring
    rw [e2]
    simp only [hD, apply_ite (algebraMap O W.EE), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_pow, map_natCast]
    unfold lE
    ring
  have hInt : ∀ m, IntA W a (∑ j, R j * algebraMap O W.EE (D j m)) := fun m =>
    intA_sum W _ _ fun j _ => intA_omul W (intA_lE W (intA_sub W (intA_add W (intA_lE W (hGint j) _)
      (intA_lE W (hε j) _)) (intA_lE W (hSnp j) _)) _) _
  set cp : Fin I → Fin d → O := fun i k =>
    if pol i then -(((PD.p : ℕ) : O) ^ (q + (t + κ₁ + κp)) * r' i k) else 0 with hcpdef
  have hfin : ∀ m, lE W (q + Mt) * F m =
      (∑ j, R j * algebraMap O W.EE (D j m)) + ∑ i, g i * algebraMap O W.EE (cp i m) := fun m => by
    rw [← hZq m]
    have e3 : ∑ i, g i * algebraMap O W.EE (cp i m) = -(lE W (q + (t + κ₁ + κp)) * Pv m) := by
      rw [hPvdef, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : pol i
      · simp only [hcpdef, if_pos hi, map_neg, map_mul, map_pow, map_natCast]
        unfold lE
        ring
      · simp only [hcpdef, if_neg hi, map_zero, mul_zero, neg_zero]
    rw [e3, hZdef]
    simp only [hMt]
    unfold lE
    ring
  refine ⟨κ₁ + (q + Mt), fun m => lE W (q + Mt) * F m, LevC.repVV_lA T₂ c' e M Λ b sol w F (q + Mt) κ₁ hF, ?_⟩
  have hS1 : SecIn W a e (LevC.condPolar (W := W) T₂ a e b)
      (fun m => ∑ j, R j * algebraMap O W.EE (D j m)) := by
    refine ⟨d, fun m₀ => ∑ j, R j * algebraMap O W.EE (D j m₀), fun m₀ => Pi.single m₀ 1, fun _ _ => 0,
      fun m₀ => ⟨?_, fun s _ => Or.inl le_rfl⟩, fun k => ?_⟩
    · obtain ⟨uu, huu, hug⟩ := hInt m₀
      show InFr W a (∏ s ∈ Finset.range e, ps W s ^ ((0 : ℤ)).toNat)
        (∏ s ∈ Finset.range e, ps W s ^ (-(0 : ℤ)).toNat) _
      simp only [neg_zero, Int.toNat_zero, pow_zero, Finset.prod_const_one]
      exact ⟨uu, huu, by rw [map_one, one_mul, hug, mul_one]⟩
    · simp [Pi.single_apply]
  have hS2 : SecIn W a e (LevC.condPolar (W := W) T₂ a e b)
      (fun m => ∑ i, g i * algebraMap O W.EE (cp i m)) := by
    refine ⟨I, g, cp, α, fun i => ⟨(hgα i).1, fun s hs => ?_⟩, fun k => rfl⟩
    by_cases hneg : α i s < 0
    · right
      have hi : pol i := ⟨s, hs, hneg⟩
      have e4 : cp i = fun k => (-((PD.p : ℕ) : O) ^ (q + (t + κ₁ + κp))) * r' i k := by
        funext k; simp only [hcpdef, if_pos hi]; ring
      rw [e4, dvO_smul]
      exact Submodule.smul_mem _ _ (hr'2 i hi s hs hneg)
    · left
      exact not_lt.mp hneg
  have hS := LevC.secIn_add W hS1 hS2
  convert hS using 1
  funext m
  rw [Pi.add_apply]
  exact hfin m

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end
end
