module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLInput
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFacts
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdealAlt
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Reduction
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightThresholdDefs
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMat
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLLaw
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen

-- Source module: Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq

open Formalism.L2.PairingIndexBounds.Eq.Sq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem sqP_of {B : Cd.Base D cc δ} (hL : B.LatAll) (hS : SqSplit B) : SqP D B.tor := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4 G hG
  obtain ⟨A, A', hP⟩ := hS N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  by_cases hG0 : G = 0
  · subst hG0
    funext v
    simp [TaylorLogMetric.Iop, TaylorLogMetric.U]
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L L'), F ≠ 0 := ⟨G, fun x hx z => hG.2 x hx z, hG0⟩
  have tripleData_of {N N' : ℕ}
      {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
      {L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
      (a1 : TaylorLogMetric.admitted D N N' L₁ L₁') (a2 : TaylorLogMetric.admitted D N N' L₂ L₂')
      (a3 : TaylorLogMetric.admitted D N N' L₃ L₃') :
      TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') (TaylorLogMetric.La D B.tor L₃ L₃') :=
    { herm := formV_herm' _ _ _ _
      sd₁ := (hL.1 N N' _ _ a1).1
      sd₂ := (hL.1 N N' _ _ a2).1
      sd₃ := (hL.1 N N' _ _ a3).1
      sc₁ := (hL.1 N N' _ _ a1).2
      sc₂ := (hL.1 N N' _ _ a2).2
      sc₃ := (hL.1 N N' _ _ a3).2
      i₁₂ := (hL.2 N N' _ _ _ _ a1 a2).1
      i₂₁ := (hL.2 N N' _ _ _ _ a1 a2).2
      i₁₃ := (hL.2 N N' _ _ _ _ a1 a3).1
      i₃₁ := (hL.2 N N' _ _ _ _ a1 a3).2
      i₂₃ := (hL.2 N N' _ _ _ _ a2 a3).1
      i₃₂ := (hL.2 N N' _ _ _ _ a2 a3).2 }
  have hT1 := tripleData_of (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h2 h3) (admissible_of_integral_conj_le hN hN' h2 h4)
  have hT2 := tripleData_of (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h1 h4) (admissible_of_integral_conj_le hN hN' h2 h4)
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ :=
    mu_one_of_split hT1 (splitTri_of hP (false, false) (true, false) (true, true) hT1) hF
  obtain ⟨T₂, T₃, hT₂, hT₃, hν⟩ :=
    mu_one_of_split hT2 (splitTri_of hP (false, false) (false, true) (true, true) hT2) hF
  funext v
  have e1 := tripleFormula _ _ _ _ _ _ hT1 S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  have e2 := tripleFormula _ _ _ _ _ _ hT2 T₂ T₃ hT₂ hT₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at e1
  rw [hν, one_mul] at e2
  exact e1.trans e2.symm

theorem eqP_of_split (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSp : SqSplit B) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  J.eqP_of_paths B hcc hδ hδ0 hS χ hχ (sqP_of (B.latAll hcc hδ hδ0) hSp) hTL hTR

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq
end
end
end

-- Source module: Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLComm

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car}

theorem mul_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {m k : 𝓞 D.host.E}
    {v : Fin N → D.host.E} (h : (k : D.host.E) • v ∈ L₁) : ((m * k : 𝓞 D.host.E) : D.host.E) • v ∈ L₁ := by
  have e : ((m * k : 𝓞 D.host.E) : D.host.E) • v = m • ((k : D.host.E) • v) := by
    rw [osmul, smul_smul]
    norm_cast
  rw [e]
  exact L₁.smul_mem m h

theorem exists_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) (x : Fin N → D.host.E) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (n : D.host.E) • x ∈ L₁ := by
  first | exact UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem .. | (apply UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ hsp x | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ hsp | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D

theorem exists_n_one {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : L.FG)
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ ∀ u ∈ L, (n : D.host.E) • u ∈ L₁ := by
  obtain ⟨s, hs⟩ := hL
  choose f hf0 hf using exists_smul_mem hsp
  refine ⟨∏ g ∈ s, f g, Finset.prod_ne_zero_iff.2 fun g _ => hf0 g, ?_⟩
  intro u hu
  rw [← hs] at hu
  induction hu using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.prod_erase_mul s f hg]
    exact mul_smul_mem (hf g)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L₁.add_mem hx hy
  | smul c x _ hx =>
    rw [osmul c x, smul_comm, ← osmul]
    exact L₁.smul_mem c hx

theorem exists_n {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) (hL1 : SD D L₁) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (∀ u ∈ L, (n : D.host.E) • u ∈ L₁) ∧ ∀ u ∈ L₁, (n : D.host.E) • u ∈ L := by
  obtain ⟨hfg, hsp, -⟩ := hL
  obtain ⟨hfg1, hsp1, -⟩ := hL1
  obtain ⟨a, ha, h1⟩ := exists_n_one hfg hsp1
  obtain ⟨b, hb, h2⟩ := exists_n_one hfg1 hsp
  refine ⟨b * a, mul_ne_zero hb ha, fun u hu => mul_smul_mem (h1 u hu), fun u hu => ?_⟩
  rw [mul_comm]
  exact mul_smul_mem (h2 u hu)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end
end

-- Source module: Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMain

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem good3 {a b c t : ℝ} (h : t = a + b + c) (ha : ∃ k : ℤ, a = 2 * k) (hb : ∃ k : ℤ, b = 2 * k)
    (hc : ∃ k : ℤ, c = 2 * k) : ∃ k : ℤ, t = 2 * k := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨l, rfl⟩ := hc
  exact ⟨i + j + l, by rw [h]; push_cast; ring⟩

theorem sqSplit_of (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hP : SplitPair D) : Sq.SqSplit B := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  obtain ⟨n, hn0, hnL, hnL1⟩ := exists_n h1 h2
  obtain ⟨e, heL', heL'', hM⟩ := hP N' L' L'' hN' h3 h4 n hn0
  have hAdm : ∀ i : Bool × Bool, TaylorLogMetric.admitted D N N' (if i.1 then L₁ else L) (if i.2 then L'' else L') := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    · exact admissible_of_integral_conj_le hN hN' h1 h3
    · exact admissible_of_integral_conj_le hN hN' h1 h4
    · exact admissible_of_integral_conj_le hN hN' h2 h3
    · exact admissible_of_integral_conj_le hN hN' h2 h4
  have hq : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, ∃ m : ℤ, qq D cc δ N N' z = m := fun i z hz =>
    Formalism.L2.Ker.Cd.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' _ _ (hAdm i) z hz
  have hsc : ∀ i, IsSemiChar (HH D cc δ N N') (Sq.sqFam B.tor L L₁ L' L'' i) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) :=
    fun i => ((B.latAll hcc hδ hδ0).1 N N' _ _ (hAdm i)).2
  have hn : ∀ a c : Bool, ∀ u ∈ (if c then L₁ else L), (n : D.host.E) • u ∈ (if a then L₁ else L) := by
    intro a c u hu
    cases a <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu ⊢
    · rw [← osmul]; exact L.smul_mem n hu
    · exact hnL1 u hu
    · exact hnL u hu
    · rw [← osmul]; exact L₁.smul_mem n hu
  have hor : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), y ∈ L' ∨ y ∈ L'' := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy
    · exact Or.inl hy
    · exact Or.inr hy
  have hin : ∀ d : Bool, ∀ m, m ∈ L' → m ∈ L'' → m ∈ (if d then L'' else L') := by
    intro d m hm1 hm2
    cases d <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact hm1
    · exact hm2
  have he : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), e *ᵥ y ∈ (if b then L'' else L') := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
    · exact heL' y hy
    · exact heL'' y hy
  have hpres : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi e z ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro i z hz
    exact phi_La (yy_mul fun A hA => homL_mul_pres (he i.2) hA) z hz
  have hMin : ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
      ∀ i j, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi M z ∈ Sq.sqFam B.tor L L₁ L' L'' j := by
    intro M hMs i j z hz
    refine phi_La (yy_mul fun A hA => homL_mul_min hn0 (hn i.1 j.1) ?_ hA) z hz
    intro y hy
    obtain ⟨m, hm1, hm2, hm⟩ := hM M hMs y (hor i.2 y hy)
    exact ⟨m, hin j.2 m hm1 hm2, hm⟩
  have hM1 : e * e - e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert _ _
  have hM2 : (letI := D.host.cmStar; eᴴ) * e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hM3 : (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e) ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

  have hidem : ∀ x : TaylorLogMetric.VC D N N', phi e x - phi e (phi e x) = -(phi (e * e - e) x) := by
    intro x
    rw [phi_sub, phi_mul]
    abel
  have hone : ∀ x : TaylorLogMetric.VC D N N', x - phi e x = phi (1 - e) x := by
    intro x
    rw [phi_sub, phi_one]
  refine ⟨AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i),
    AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i), ?_⟩
  have hA : ∀ x, x ∈ AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, x - phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  have hA' : ∀ x, x ∈ AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx' i
    have := (Sq.sqFam B.tor L L₁ L' L'' i).add_mem ((hA x).1 hx i) ((hA' x).1 hx' i)
    rwa [sub_add_cancel] at this
  · intro i x hx
    refine ⟨phi e x, (hA _).2 fun j => ?_, x - phi e x, (hA' _).2 fun j => ?_, hpres i x hx,
      (Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hx (hpres i x hx), (add_sub_cancel _ _).symm⟩
    · rw [hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
    · rw [map_sub, hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (phi e x) (phi e y) +
        bet D cc δ N N' (phi e x) (y - phi e y) + bet D cc δ N N' (x - phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (phi e x) (x - phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (phi e x) (phi e y) (y - phi e y)
      rw [add_sub_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM2 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) (hpres i x hxi) ((hA y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA x).1 hx j) hyj
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (x - phi e x) (y - phi e y) +
        bet D cc δ N N' (x - phi e x) (phi e y) + bet D cc δ N N' (phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (x - phi e x) (phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (x - phi e x) (y - phi e y) (phi e y)
      rw [sub_add_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [hone x, hone y, bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM3 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) ((Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hxi ((hA' x).1 hx i)) ((hA' y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA' x).1 hx j) hyj

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end
end

-- Source module: Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLTop

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of_pair (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hP : SplitPair D) : B.EqP χ := by
  exact Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ (sqSplit_of B hcc hδ hδ0 hP)
    (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end
end

-- Source module: Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen

section

@[expose] public section

noncomputable section
open NumberField Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG

open Formalism.L2.PairingIndexBounds.Eq.SqG

theorem splitPair_of_gen (h : SplitPairGen) (D : Formalism.L2.Ker.Car) : SquareSplitPairs.SplitPair D := by
  have hCM : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
  have hcj : ∀ y : D.host.E, D.host.conj y = star y := by
    intro y
    obtain ψ := Classical.choice (inferInstance : Nonempty (D.host.E →+* ℂ))
    apply ψ.injective
    rw [Formalism.HC.HostAx.conjE_apply D.host.toHostAx ψ y]
    exact (NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ y).symm
  have hU : PI.IsCMUnram D.host.E := by
    refine ⟨hCM.to_isTotallyComplex, fun φ a => ?_, fun P hP => ?_⟩
    · rw [← hcj]
      exact Formalism.HC.HostAx.conjE_apply D.host.toHostAx φ a
    · have hne : P ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField _)
      have h2 := Formalism.HC.HostDer.unramEF D.host.der P hP.isPrime hne
      push_neg at h2
      obtain ⟨x, hx⟩ := h2
      refine ⟨x, D.host.conj • x, ?_, ?_⟩
      · exact hcj (x : D.host.E)
      · intro hm
        apply hx
        have h3 : D.host.conj • x - x = -(x - D.host.conj • x) := by ring
        rw [h3]
        exact P.neg_mem hm
  intro N' L' L'' hN hL' hL'' n hn
  exact h D.host.E hU N' L' L'' hN hL' hL'' n hn

theorem eqP_gen {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Cd.Base D cc δ)
    (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0) (hS : B.StdOK)
    (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsChi D χ) (hG : SplitPairGen) : B.EqP χ :=
  SquareSplitPairs.eqP_of_pair B hcc hδ hδ0 hS χ hχ (splitPair_of_gen hG D)

theorem delta_ne {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := Formalism.L2.Ker.Cd.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ

theorem eqP_all {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Cd.Base D cc δ) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hS : B.StdOK) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsChi D χ) (hP : SplitPairGen) : B.EqP χ :=
  eqP_gen B hcc hδ (delta_ne hcc hδ) hS χ hχ hP

theorem eqP_car {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Cd.Base D cc δ) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsChi D χ) : B.EqP χ :=
  eqP_all B hcc hδ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ split_pair_generation

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG

end
end
end
