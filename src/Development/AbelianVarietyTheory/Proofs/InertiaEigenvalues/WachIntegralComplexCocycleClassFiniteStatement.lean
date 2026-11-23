module

public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystallineStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulLeft
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachModuleOfXPowSmulFrobeniusGammaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulMemWachModuleOfFrobenius

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


namespace GlobalTheory.NL.DenomStep

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem mem_N_of_jD (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (h1 : p1et W E T)
    (h6 : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (x : W.DD T) (hx : E.jD T x ∈ NAinf W E T) : x ∈ W.N T := by
  obtain ⟨⟨r, b, hbN, hbA, hbW⟩, -⟩ := h1

  have hNA : ∀ z ∈ NAinf W E T, ∃ β : Fin r → RA, z = ∑ j, inclR (β j) • E.jD T (b j) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hxN, rfl⟩ := hz
      obtain ⟨α, hα, -⟩ := hbA x hxN
      refine ⟨fun j => a * E.io (α j), ?_⟩

      rw [hα, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [GlobalTheory.NL.FrobDenom.jD_smulA, smul_smul, map_mul]
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨β, rfl⟩ := hz
      obtain ⟨γ, rfl⟩ := hw
      refine ⟨β + γ, ?_⟩
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, map_add (f := _), add_smul]
    | smul c z _ hz =>
      obtain ⟨β, rfl⟩ := hz
      refine ⟨c • β, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, map_smul, smul_assoc]

  have hDE : ∀ y : W.DD T, ∃ μ : Fin r → W.EE, y = ∑ j, μ j • b j := by
    intro y
    refine (W.N_base T hT).inductionOn y ?_ ?_ ?_
    · intro z
      obtain ⟨α, hα, -⟩ := hbA z z.2
      refine ⟨fun j => algebraMap _ W.EE (α j), ?_⟩
      simp only [Submodule.subtype_apply, algebraMap_smul]
      exact hα
    · rintro e y ⟨μ, rfl⟩
      exact ⟨e • μ, by simp [Finset.smul_sum, smul_smul]⟩
    · rintro y y' ⟨μ, rfl⟩ ⟨μ', rfl⟩
      exact ⟨μ + μ', by simp [add_smul, Finset.sum_add_distrib]⟩
  obtain ⟨β, hβ⟩ := hNA _ hx
  obtain ⟨μ, rfl⟩ := hDE x
  have hj : E.jD T (∑ j, μ j • b j) = ∑ j, E.ioE (μ j) • E.jD T (b j) := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => E.jD_smul T _ _
  obtain ⟨c, -, hc⟩ := hbW (E.jD T (∑ j, μ j • b j))
  have e1 := hc (fun j => E.ioE (μ j)) hj
  have e2 := hc (fun j => inclR (β j)) hβ
  have hμ : ∀ j, ∃ a : LetA O n, algebraMap _ W.EE a = μ j := fun j =>
    h6 (μ j) ⟨β j, (congrFun e2 j).trans (congrFun e1 j).symm⟩
  choose a ha using hμ
  have : ∑ j, μ j • b j = ∑ j, a j • b j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, algebraMap_smul]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbN j)

end Generic

end GlobalTheory.NL.DenomStep

namespace GlobalTheory.NL.DenomStep

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem of_tie (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (hF : ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T →
      ∀ b : TW RW T, TWmap φR T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ,
        TensorProduct.map (LinearMap.mulLeft O
          (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
          TAinf inclR T)
    (hP1 : p1et W E T ∧ wachInfiniteLevel W E T)
    (h6 : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (M : ℕ) (m : W.DD T) (hm : W.φD T m - m ∈ invN W T (W.Q ^ M)) :
    ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  have hy : ((Multiset.replicate M 0).map fun j => (W.φA ^ j) W.Q).prod • (W.φD T m - m) ∈
      W.N T := by
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hm
  have hb : TWmap φR T (E.jD T m) - E.jD T m = E.jD T (W.φD T m - m) := by
    rw [map_sub, E.jD_φ]
  obtain ⟨a, ha⟩ := hF _ _ hy _ hb 0 (fun j hj => (Multiset.eq_of_mem_replicate hj).le)
  rw [Finset.prod_range_one, pow_zero, GlobalTheory.NL.SandArb.map_mulLeft] at ha
  obtain ⟨h1, k, hk, -⟩ := hP1
  have hz := hk _ ha
  refine ⟨k + a, mem_N_of_jD E T hT h1 h6 _ ?_⟩
  rw [GlobalTheory.NL.FrobDenom.jD_smulA, map_pow, map_pow, pow_add, mul_smul]
  exact hz

end Generic



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  intro D HW F l _ K s LL h W T hT M m hm
  exact of_tie ((F l).E K s LL h).tie T hT (GlobalTheory.NL.FrobDenom.main D HW F l K s LL h T hT)
    (GlobalTheory.NL.NygaardExtension.main D HW F l K s LL h T hT) (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.1 M m hm

end GlobalTheory.NL.DenomStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulMemWachModuleOfFrobeniusStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  first | exact @GlobalTheory.NL.DenomStep.main | exact GlobalTheory.NL.DenomStep.main | (intros; apply GlobalTheory.NL.DenomStep.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGamma

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CocycleInj



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  intro D HW F l _ K s LL h W E T hT M m hy hz
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius D HW F l K s LL h T hT M m hy
  exact GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma D HW F l K s LL h T hT M a m hy hz ha

end GlobalTheory.NL.CocycleInj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGammaStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.mem_wach_of_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.CocycleInj.main | exact GlobalTheory.NL.CocycleInj.main | (intros; apply GlobalTheory.NL.CocycleInj.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFinite

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntComplex



theorem ring_part (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) :
    let W := (HW l).W K s LL h
    (∃ w, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X}) ∧ ∃ b, W.X = letπ * b := by
  intro W
  obtain ⟨χ, -, -, hγ, hX, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have hs : 1 ≤ s := h.1
  obtain ⟨-, -, -, -, -, hact, -⟩ := GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s hs
  obtain ⟨-, b, hb⟩ := hact (χ W.gam)
  refine ⟨⟨1 + W.X * fun _ => b, ?_, ?_⟩, ?_⟩
  · funext i
    change W.γ₀ W.gam (W.Q i) = (1 + W.X i * b) * W.Q i
    rw [hγ, hX, hQ, hb, mul_comm]
  · rw [add_sub_cancel_left]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  · obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries ↥(OL LL)) ∣ GlobalTheory.Cyc.XX l ↥(OL LL) s := by
      rw [PowerSeries.X_dvd_iff, GlobalTheory.Cyc.XX]
      simp
    refine ⟨fun _ => c, ?_⟩
    funext i
    change W.X i = PowerSeries.X * c
    rw [hX, hc]



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  intro D HW F l _ K s LL h T M hh hT _
  obtain ⟨h1, b, hb⟩ := ring_part D HW l K s LL h
  refine ⟨h1, fun y z hy hz hc => ?_⟩
  have hz' : z ∈ aN ((HW l).W K s LL h) T letπ := by
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨b • x, Submodule.smul_mem _ b hx, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hb, mul_smul]
  refine ⟨?_, fun h0 => ?_⟩
  · refine GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F l K s LL h T hT (Multiset.replicate (mx M) 0) y z ?_ hz' hc
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hy
  · obtain ⟨m, hm⟩ := ((GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F l K s LL h T hT).1.2 ⟨(y, z), hc⟩).1 h0
    have hm1 : y = ((HW l).W K s LL h).φD T m - m := congrArg Prod.fst hm
    have hm2 : z = ((HW l).W K s LL h).γ T m - m := congrArg Prod.snd hm
    refine ⟨m, GlobalTheory.T.mem_wach_of_frobenius_gamma D HW F l K s LL h T hT (mx M) m ?_ ?_, hm1, hm2⟩
    · exact hm1 ▸ hy
    · exact hm2 ▸ hz'

end GlobalTheory.NL.IntComplex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFiniteStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachIntegralComplex_cocycle_class_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  first | exact @GlobalTheory.NL.IntComplex.main | exact GlobalTheory.NL.IntComplex.main | (intros; apply GlobalTheory.NL.IntComplex.main <;> assumption)
end
end
