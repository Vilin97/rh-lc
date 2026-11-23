module

public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.GCoordProp
import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
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
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CompleteMax
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerUnitAndQFactor
public import Formalism.SharpRestriction.LevelLetterCocycles.DvOZeroHigh
public import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.TmulMemFilV
import Mathlib.RingTheory.PowerSeries.Inverse
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerCongruenceOfAdmitted
public import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
public import Formalism.SharpRestriction.LevelLetterCocycles.RingClausesAtUniformizer
public import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.At0HomApply

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def at0Hom (W : LocWach PD LL O v n) (hz : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries O →+* LetA O n where
  toFun := Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W
  map_one' := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C W (1 : O)
    rw [map_one, map_one] at this
    exact this
  map_mul' := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_mul W hz
  map_zero' := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C W (0 : O)
    rw [map_zero, map_zero] at this
    exact this
  map_add' := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evaluation_add W hz

theorem at0Hom_apply (W : LocWach PD LL O v n) (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f : PowerSeries O) :
    at0Hom W hz f = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := rfl

theorem gCoord_holds (W : LocWach PD LL O v n) : GCoordProp W := by
  intro T i h c r e e' he P Z hP hz hqpu k hg hgDL a ha l
  classical
  have hqp : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = Formalism.MainNotions.LiftingTheory.qp W := by
    rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evaluation_add W hz, Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_X_eq_pi0 W hz, Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C, map_natCast]
    rfl
  set x := Formalism.MainNotions.LiftingTheory.qp W ^ c • Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k with hx
  have hxN : x ∈ W.N T := (W.N T).smul_mem _ hg
  have hxDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := by
    refine ⟨by rw [hx, smul_comm, hgDL.1], fun δ hδ => ?_⟩
    rw [hx, Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA, map_pow,
      Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.qp_mem W (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) δ hδ, hgDL.2 δ hδ]

  have e1 : x = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) • e l := by
    rw [hx, ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    rw [show Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) =
      at0Hom W hz ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) from rfl, map_mul, map_pow,
      at0Hom_apply, at0Hom_apply, hqp]

  have hcancel : x = Formalism.MainNotions.LiftingTheory.qp W ^ h • Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.ftE W T e' Z k := by
    rw [hx, Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE, ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow,
      ← mul_pow, Ring.mul_inverse_cancel _ hqpu, one_pow, one_smul]
  have e2 : x = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((P * Z) l k) • e l := by
    rw [hcancel, Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.ftE, Finset.smul_sum]
    simp only [pow_one]
    have : ∀ m₁, Formalism.MainNotions.LiftingTheory.qp W ^ h • (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Z m₁ k) • W.φD T (e' m₁)) =
        ∑ l, (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Z m₁ k) * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (P l m₁)) • e l := by
      intro m₁
      rw [smul_comm, hP m₁, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_

    rw [← Finset.sum_smul, Matrix.mul_apply, ← at0Hom_apply W hz, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [map_mul, at0Hom_apply, at0Hom_apply, mul_comm]
  have huniq := (he.2 x hxN hxDL).unique e1.symm.symm e2
  exact congrFun huniq l

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DlOfQp

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GM

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem filLev_anti (T : LocLat G Qp LL O) (i : ZMod n) :
    Antitone fun a : ℤ => Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro a b hab
  exact Submodule.map_mono (Submodule.map_mono
    (inf_le_inf_right _ fun x hx => Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hab hx))

theorem ιDi_le_fil (hbij : Function.Bijective (algebraMap K₀ K)) (T : LocLat G Qp LL O) (i : ZMod n)
    (H : ℕ) (hJ : ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a)
    (a : ℤ) (ha : a ≤ -(H : ℤ)) : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ≤ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨τ, hτ, hover⟩ := Formalism.MainNotions.UnusedSlot80.LevC.tau_over W hbij i
  have h1 := Formalism.MainNotions.UnusedSlot80.LevC.fil_low W T i τ hover hbij.2 H (hJ τ hτ) hx
  have h2 := Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ ha h1
  refine ⟨x, ⟨x, ⟨h2, by simpa using hx⟩, by simp⟩, rfl⟩

theorem qp_smul_gE (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (h c : ℕ) {r : ℕ} (e' : Fin r → W.DD T) (Z : Matrix (Fin r) (Fin r) (PowerSeries O)) (k : Fin r) :
    Formalism.MainNotions.LiftingTheory.qp W ^ c • gE W T h c e' Z k = Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T e' Z k := by
  unfold gE
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow, ← mul_pow,
    Ring.mul_inverse_cancel _ hq, one_pow, one_smul]

theorem qp_pow_inj (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (c : ℕ) (z : W.DD T) (hz : Formalism.MainNotions.LiftingTheory.qp W ^ c • z = 0) : z = 0 := by
  calc z = ((Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c *
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ c) • z := by
          rw [← mul_pow, Ring.inverse_mul_cancel _ hq, one_pow, one_smul]
    _ = (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c •
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c) • z) := by rw [smul_smul, map_pow]
    _ = 0 := by rw [algebraMap_smul, hz, smul_zero]

theorem qp_mem_AΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) (W.AΔ.natCast_mem _)

theorem dl_of_qp (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (i : ZMod n) (c : ℕ) (g y : W.DD T) (hgy : Formalism.MainNotions.LiftingTheory.qp W ^ c • g = y)
    (hy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i y) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i g := by
  constructor
  · apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ c) (letE i : LetA O n) g, hgy, hy.1, sub_self]
  · intro δ hδ
    apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    have hA : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) = Formalism.MainNotions.LiftingTheory.qp W ^ c :=
      W.AΔ.pow_mem (qp_mem_AΔ W) c δ hδ
    have e := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) g
    rw [hA, hgy, hy.2 δ hδ] at e
    rw [smul_sub, ← e, hgy, sub_self]

theorem ring_clauses_at_uniformizer (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W := by
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨-, -, h9'⟩ := h9 T hT hA.2.1 hA.2.2
  obtain ⟨hring, -⟩ := h9' hfin1
  exact hring

theorem gE_mem (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W)
    {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) (hi : i ∈ evens n d)
    (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ)
    (had : AdaptData W T₂ i (b i + S) η m e' m' u) (σ : ℕ) (Z : Matrix _ _ (PowerSeries O))
    (hZP : ZProps W T₂ i (b i + S + η) σ e' had.1 Z) (j : Fin m') (hmr : m' ≤ finrank LL T₂.V) :
    gE W T₂ (b i + S) ((b i + S : ℕ) + u j).toNat e' Z (Fin.castLE hmr j) ∈ NDl W T₂ i := by
  have hie : (i.val + d) % 2 = 0 := (Finset.mem_filter.1 hi).2
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hl11 : 11 ≤ PD.p := hS.2.1
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  obtain ⟨-, hπu, w, hw⟩ := DetS.uniformizer_unit_and_q_factor W h9 hCA T₂ hT (by omega)
  have hq := DetS.qp_unit W hπu
  have hR9 := ring_clauses_at_uniformizer W h9 hCA T₂ hT
  obtain ⟨-, -, hmr', hwin, hfil, -⟩ := id had
  have hηb := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
  set h : ℕ := b i + S with hhdef
  set k : Fin (finrank LL T₂.V) := Fin.castLE hmr j with hkdef
  set c : ℕ := ((h : ℤ) + u j).toNat with hcdef
  have hc : (c : ℤ) = h + u j := Int.toNat_of_nonneg (by have := (hwin j).1; omega)

  have hyN : Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k ∈ NDl W T₂ i := by
    unfold ftE
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun m₁ _ => ?_
    rw [smul_comm, pow_one]
    have hm := DetA.qpφ_mem W hE hC hQ h5 h9 hS i hie e' had.1 m₁
    have ha := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR9 (Z m₁ k)
    refine ⟨(W.N T₂).smul_mem _ hm.1, ?_, fun δ hδ => ?_⟩
    · rw [smul_comm (letE i : LetA O n), hm.2.1]
    · rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T₂ δ, ha δ hδ, hm.2.2 δ hδ]
  have hgy := qp_smul_gE W hq T₂ h c e' Z k
  have hgDL := dl_of_qp W hq T₂ i c _ _ hgy hyN.2

  obtain ⟨u0, hlq, hu0⟩ := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lev_q_X_mul W i ζ hζ (by omega)
    (Formalism.MainNotions.N.Pv.LocalLengthBound.p_ne_zero_LL W)
  set U : PowerSeries LL := W.lev i ζ ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * u0 with hUdef
  have hwq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) = PowerSeries.X * U := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hlq, hUdef]; ring
  have hU : PowerSeries.constantCoeff U ≠ 0 := by
    rw [hUdef, map_mul]
    refine mul_ne_zero ?_ hu0
    exact (PowerSeries.isUnit_iff_constantCoeff.1 ((Units.isUnit _).map (W.lev i ζ))).ne_zero
  have hU0 : U ≠ 0 := fun h0 => hU (by rw [h0, map_zero])
  have hlevpow : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) = PowerSeries.X ^ t * U ^ t := by
    intro t; rw [map_pow, hwq, mul_pow]
  have hlevne : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) ≠ 0 := by
    intro t; rw [hlevpow]; exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hU0)

  obtain ⟨hEx, hDi, -, -, hconv, -, -⟩ := hRu hCA T₂ hT i ζ hζ
  obtain ⟨df, hdf, -⟩ := hEx (ftE W T₂ e' Z k) _ hyN.1 (hlevne h)
  obtain ⟨dg, hdg, -⟩ := hEx (gE W T₂ h c e' Z k) (Formalism.MainNotions.LiftingTheory.qp W ^ c) (by rw [hgy]; exact hyN.1)
    (hlevne c)
  have hy1 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ h) _ df hdf
  have hy2 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ c) _ dg hdg
  rw [hgy] at hy2
  have huniq := (hEx (Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k) 1 (by rw [one_smul]; exact hyN.1)
    (by rw [map_one]; exact one_ne_zero)).unique hy2 hy1
  obtain ⟨mg, hmg⟩ := hdg.1
  have hi1 : i - 1 + ((1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hZ := hZP.2 k ζ hζ df (by rw [hi1]; exact hdf)
  have hv : ιV PD (LL := LL) (V := T₂.V) ((φVB PD (LL := LL) (V := T₂.V))^[1]
      (W.cmp T₂ ⟨e' k, (had.1.1 k).1⟩)) ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (u j) := by
    rw [Function.iterate_one]; exact hfil j _
  set Fil : ℤ → Submodule LL (T₂.V ⊗[Qp] BdR) := fun a => Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a with hFil
  have hanti : Antitone Fil := filLev_anti W T₂ i
  have hLBf : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB 0 df := by
    intro t ht
    rw [hZ t (by omega), ite_eq_right (by omega)]
  set Ff := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ h) df with hFf
  set E := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c) dg with hEdef
  have hF_mem : ∀ s : ℤ, s < ((h + η : ℕ) : ℤ) → Ff s ∈ Fil (u j) := by
    intro s hs
    rw [hFf, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_eq_sum hLBf (U ^ h) s (s.toNat + 1)
      (by have := Int.self_le_toNat s; omega)]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    rw [hZ _ (by omega)]
    split_ifs
    · exact Submodule.smul_mem _ _ hv
    · exact Submodule.zero_mem _
  have hF_neg : ∀ s : ℤ, s < 0 → Ff s = 0 := fun s hs =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf (U ^ h) s hs
  have hEF : ∀ t : ℤ, E t = Ff (t + u j) := by
    intro t
    have e1 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ c)) dg = fun s => E (s - c) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hmg,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _)]
    have e2 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ h)) df = fun s => Ff (s - h) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hLBf,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf _)]
    have e3 := congrFun huniq (t + c)
    rw [e1, e2] at e3
    simp only at e3
    rw [show t + (c : ℤ) - c = t by ring, show t + (c : ℤ) - h = t + u j by omega] at e3
    exact e3
  have hEDi : ∀ t, E t ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i := fun t =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.smulS_mem hmg _ (hDi _ dg hgDL hdg) (U ^ c) t
  have hlow : ∀ a : ℤ, a ≤ -(h : ℤ) → Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ Fil a := by
    intro a ha
    refine ιDi_le_fil W hCA.1 T₂ i h (fun τ hτ a' ha' => ?_) a ha
    have hw2 := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a' ha'
    unfold JumpWinS at hw2
    rw [ite_eq_left hie] at hw2
    simp only [Set.mem_union, Set.mem_Icc] at hw2
    rw [hhdef]; push_cast at hw2 ⊢
    omega
  have hDgE : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 E := by
    intro t
    by_cases ht : t + u j < ((h + η : ℕ) : ℤ)
    · rw [hEF t]
      by_cases h0 : t + u j < 0
      · rw [hF_neg _ h0]; exact Submodule.zero_mem _
      · exact hanti (show 0 - t ≤ u j by omega) (hF_mem _ ht)
    · exact hlow (0 - t) (by have := (hwin j).2; push_cast at ht; omega) (hEDi t)
  have hUc : PowerSeries.constantCoeff (U ^ c) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hU
  have hdg_eq : dg = Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c)⁻¹ E :=
    (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_inv hmg (U ^ c) hUc).symm
  have hDg : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 dg := by
    rw [hdg_eq]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg_smulS hanti (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _) hDgE _
  have hcrit := (hEC hCA T₂ hT i ζ hζ _ dg hgDL hdg).1 ⟨c, by rw [hgy]; exact hyN.1⟩
  refine ⟨hcrit.2 fun t => ?_, hgDL⟩
  have := hDg t
  simpa [hFil] using this

theorem gMem_of (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) : GMem W :=
  fun _ _ _ _ _ _ _ _ hS i hi e' m' u had σ Z hZP j hmr =>
    gE_mem W hE hC hQ h5 h9 hRu hEC hS i hi e' m' u had σ Z hZP j hmr

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GM
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmitted

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩



theorem dual_lemma_of_admitted (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] : LemmaDN ((HW l).W K 1 LL hg) := by
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.complete_max LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBall : ∀ (l' : ℕ) [Fact l'.Prime] (K' LL' : FinExt l') (hg' : Good K' 1 LL')
      [NeZero (Module.finrank ℚ_[l'] ↥(K0 K'))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l').W K' 1 LL' hg') := by
    intro l' _ K' LL' hg' _
    haveI : IsFractionRing ↥(OL LL') ↥LL'.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL'
    exact Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ (hA.1 l' K' 1 LL' hg').2.2.2.2.2.2.2.2.1
  have hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_D' D HW F Cm CR CA CB CK hA hL hBall l K LL hCAl h5l
  have hGM := Formalism.MainNotions.RamifiedCoefficientChains.S9.GM.gMem_of W hE hC hQ h1.2.2.2.2.1 h9 hRu hEC
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_local D HW F Cm hA.1 l K LL hg
  have hZ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.zTool_of W h9 (((Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.truncation_clause_of_lattice_hypotheses D HW F Cm (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1).2 l K LL hg).2) hTH hBas hRu
    hRing hΔ
  have hAd : Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.AdaptBas W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.AdM.adaptBas_of W hE hC hQ h1.2.2.1 h1.2.2.2.2.1 h9 (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [hpl]; exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  have hPt : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      IsPrimitiveRoot ζ ((D.loc l).PD K).p →
      ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg i ζ τ := by
    intro _ c ζ hζ
    obtain ⟨τ, hτ⟩ := hpt l K LL hCAl h5l c ζ (by rwa [hpl] at hζ)
    refine ⟨τ, ?_, hτ⟩
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    apply AlgHom.ext
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    show τ (algebraMap ↥(K0 K) ↥K.1 x) = _
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have hDT : Formalism.MainNotions.RamifiedCoefficientChains.Sh.DetTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.detTool_of W h9 _ h1.2.2.2.1 hPt hQ hpm hset.2.2.2.2.1
  have hDet := Formalism.MainNotions.RamifiedCoefficientChains.S9.DetA.detAlg_of W hE hC hQ h1.2.2.2.2.1 h9 hBas (fun _ => hDT)
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord.gCoord_holds W)
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.lemmaDN_of_S1E W hZ hAd hGM hDet d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral
end
end
end
