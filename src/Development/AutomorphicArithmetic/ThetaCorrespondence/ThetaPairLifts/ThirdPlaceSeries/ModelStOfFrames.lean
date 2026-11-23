module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineLatticeLinkOfBlockDataStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
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
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealsMeetingSubspaceCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStatementOfFrameGalois

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFrameCoeffRingQuotientPrime

section

@[expose] public section

open GlobalTheory.ExpFrame Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.FrameQuot

theorem finite_quot_prime (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N) (hF : F.Ok) :
    Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  obtain ⟨hinj, L, hL, hrange⟩ := hF.ring
  haveI := hL
  have hmem : ∀ x : F.O, F.emb x ∈ L ∧ ‖F.emb x‖ ≤ 1 := fun x => by
    have hx : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at hx
    exact hx
  let f : F.O →+* integralClosure ℤ_[l] L :=
    { toFun := fun x => ⟨⟨F.emb x, (hmem x).1⟩,
        (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨F.emb x, (hmem x).1⟩).2 (hmem x).2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one F.emb))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul F.emb x y))
      map_zero' := Subtype.ext (Subtype.ext (map_zero F.emb))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add F.emb x y)) }
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨y, hyL⟩, hy⟩
    have hn := (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨y, hyL⟩).1 hy
    have hy' : y ∈ Set.range F.emb := by
      rw [hrange]
      exact ⟨hyL, hn⟩
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, rfl⟩
  have hbij : Function.Bijective f :=
    ⟨fun x y h => hinj (congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : PadicAlgCl l)) h), hsurj⟩
  let e := RingEquiv.ofBijective f hbij
  have hfin : Finite (integralClosure ℤ_[l] L ⧸
      Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1}) :=
    GlobalTheory.LocalIntegers.finite_quotient_pow l (integralClosure ℤ_[l] L) 1
  have hIJ : Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1} =
      (Ideal.span {((l : ℕ) : F.O)}).map (e : F.O →+* integralClosure ℤ_[l] L) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, pow_one]
  exact Finite.of_equiv _ (Ideal.quotientEquiv _ _ e hIJ).symm.toEquiv

end GlobalTheory.FrameQuot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFrameCoeffRingQuotientPrimeStatement

section

@[expose] public section

open GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.finite_frameCoeffRing_quotient_prime : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  first | exact @GlobalTheory.FrameQuot.finite_quot_prime | exact GlobalTheory.FrameQuot.finite_quot_prime | (intros; apply GlobalTheory.FrameQuot.finite_quot_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnit

section

@[expose] public section

open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpFrame

theorem Frame.prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  intro l _ ι N F hF hu
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  obtain ⟨L, -, hL⟩ := hF.ring.2
  have hmem : F.emb u ∈ Set.range F.emb := ⟨u, rfl⟩
  rw [hL] at hmem
  have h1 : F.emb u * (l : PadicAlgCl l) = 1 := by
    have := congrArg F.emb hu
    rwa [map_mul, map_natCast, map_one] at this
  have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.norm_p]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one, hl] at h2
  have hlgt : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  have h3 : ‖F.emb u‖ * (l : ℝ)⁻¹ < 1 := by
    calc ‖F.emb u‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ := by gcongr; exact hmem.2
      _ = (l : ℝ)⁻¹ := one_mul _
      _ < 1 := inv_lt_one_of_one_lt₀ hlgt
  linarith

end GlobalTheory.ExpFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnitStatement

section

@[expose] public section

open GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.frameCoeffRing_prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.prime_not_isUnit | exact GlobalTheory.ExpFrame.Frame.prime_not_isUnit | (intros; apply GlobalTheory.ExpFrame.Frame.prime_not_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasBlocksOfSystemOccursInBlockPart

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.OccBlock

open Module Module.End

section Gen

variable {L V J : Type} [Field L] [DecidableEq L] [AddCommGroup V] [Module L V]

def jointGen (T : J → End L V) (y : J → L) : Submodule L V := ⨅ j, (T j).maxGenEigenspace (y j)

theorem mem_iSup_filter (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y) {θ : J → L} {f : V}
    (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (j : J) (hY : f ∈ ⨆ y ∈ Y, p y) :
    f ∈ ⨆ y ∈ Y.filter (fun y => y j = θ j), p y := by
  have hsplit : (⨆ y ∈ Y, p y) ≤ (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ⊔
      (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) := by
    refine iSup₂_le fun y hy => ?_
    by_cases h : y j = θ j
    · exact le_sup_of_le_left (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
    · exact le_sup_of_le_right (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hsplit hY)
  have hA : (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ≤ (T j).maxGenEigenspace (θ j) := by
    refine iSup₂_le fun y hy => ?_
    have hyj := (Finset.mem_filter.1 hy).2
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ = (T j).maxGenEigenspace (θ j) := by rw [hyj]
  have hB : (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) ≤ ⨆ (μ : L) (_ : μ ≠ θ j), (T j).maxGenEigenspace μ := by
    refine iSup₂_le fun y hy => ?_
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ ≤ _ := le_biSup (fun μ => (T j).maxGenEigenspace μ) (show y j ∈ {μ | μ ≠ θ j} from (Finset.mem_filter.1 hy).2)
  have hfθ : f ∈ (T j).maxGenEigenspace (θ j) := by
    rw [mem_maxGenEigenspace]
    exact ⟨1, by simp [hf j]⟩
  have hb0 : b = 0 := by
    have hb1 : b ∈ (T j).maxGenEigenspace (θ j) := by
      have hbe : b = f - a := by rw [← hab]; abel
      rw [hbe]
      exact Submodule.sub_mem _ hfθ (hA ha)
    exact (Submodule.disjoint_def.1 ((Module.End.independent_maxGenEigenspace (T j)) (θ j))) b hb1 (hB hb)
  rw [← hab, hb0, add_zero]
  exact ha

theorem mem_of_mem_iSup_finset (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y)
    {θ : J → L} {f : V} (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (hY : f ∈ ⨆ y ∈ Y, p y) : f ∈ p θ := by
  induction Y using Finset.strongInduction with
  | H Y ih =>
    by_cases h : ∃ y ∈ Y, y ≠ θ
    · obtain ⟨y0, hy0, hne⟩ := h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      exact ih _ (Finset.filter_ssubset.2 ⟨y0, hy0, hj⟩) (mem_iSup_filter T p hp hf Y j hY)
    · push_neg at h
      exact (iSup₂_le fun y hy => by rw [h y hy] : (⨆ y ∈ Y, p y) ≤ p θ) hY

end Gen

section Read

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)

def heckeQ (i : F.I) : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by
    funext g
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by
    funext g
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul, smul_smul, mul_comm]

variable {F lam} {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  {B : BlockDat K G0 Pl0} {w : HeightOneSpectrum (𝓞 K)}

theorem rd_pow (R : Reads F lam B w) (i : F.I) (a : K) (k : ℕ) (v : B.S.Forms) :
    R.rd (((B.op (R.ix i) - a • (1 : End K B.S.Forms)) ^ k) v) =
      ((heckeQ F lam i - R.e0 a • (1 : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam))) ^ k) (R.rd v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    funext g
    simp [map_sub, map_smulₛₗ, R.hecke, heckeQ]

end Read

theorem hasBlock_of_occurs : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type)
    (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) →
    Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  intro K _ _ _ G0 _ _ Pl0 B w l _ ι _ N F lam R Z hop hZ θ hocc
  obtain ⟨f, hfspan, hfe⟩ := hocc
  refine ⟨?_, ⟨f, hfe⟩⟩
  classical
  let S : Set (F.I → PadicAlgCl l) :=
    {y | ∃ x : B.Pl × ℕ → K, (∀ P, x (P, 0) = 1) ∧ Formalism.L2.Col.HasBlocks B.n B.q B.t B.bl x ∧ ∀ i, y i = R.e0 (x (R.ix i))}
  let p : (F.I → PadicAlgCl l) → Submodule (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) :=
    fun y => ⨆ (_ : y ∈ S), jointGen (heckeQ F lam) y
  have hp : ∀ y, p y ≤ jointGen (heckeQ F lam) y := fun y => iSup_le fun _ => le_rfl
  have key : B.ZH ≤ (⨆ y, p y).comap R.rd := by
    rw [BlockDat.ZH, Formalism.L2.Col.blockSum, Formalism.L2.Col.eigSum]
    refine iSup₂_le fun x hx => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
      exact Submodule.zero_mem _
    have hx1 : ∀ P, x (P, 0) = 1 := fun P =>
      GlobalTheory.ExpFrame.eq_one_of_occurs (op := B.op) ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩) (hop P)
    refine Submodule.mem_iSup_of_mem (fun i => R.e0 (x (R.ix i))) ?_
    refine Submodule.mem_iSup_of_mem (show (fun i => R.e0 (x (R.ix i))) ∈ S from ⟨x, hx1, hx, fun i => rfl⟩) ?_
    rw [jointGen, Submodule.mem_iInf]
    intro i
    have hv' := Formalism.L2.Col.eigAt_le B.op x (R.ix i) hv
    rw [mem_maxGenEigenspace] at hv' ⊢
    obtain ⟨k, hk⟩ := hv'
    exact ⟨k, by rw [← rd_pow, hk, map_zero]⟩
  have hspan : Submodule.span (PadicAlgCl l) (R.rd '' Z) ≤ ⨆ y, p y := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact key (hZ hz)
  obtain ⟨Y, hY⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hspan hfspan)
  have hf : ∀ i, heckeQ F lam i f = θ i • f := fun i => by
    funext g
    exact hfe.2.2 i g
  have hθ := mem_of_mem_iSup_finset (heckeQ F lam) p hp hf Y hY
  by_cases hθS : θ ∈ S
  · exact hθS
  · exfalso
    have h0 : p θ = ⊥ := by simp [p, hθS]
    rw [h0, Submodule.mem_bot] at hθ
    exact hfe.1 hθ

end GlobalTheory.OccBlock

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasBlocksOfSystemOccursInBlockPartStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) → Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  first | exact @GlobalTheory.OccBlock.hasBlock_of_occurs | exact GlobalTheory.OccBlock.hasBlock_of_occurs | (intros; apply GlobalTheory.OccBlock.hasBlock_of_occurs <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStOfFrames

section

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization GlobalTheory.ExpModel
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem atPts_and2_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (h' : _root_.GlobalTheory.BigOn.AtPtsAlt Q') : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (Closed.and h h') fun _ _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm => ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm,
      hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩
theorem atPts_mono_of_more {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), More p →
      Q Fm x hx i p → Q' Fm x hx i p) : _root_.GlobalTheory.BigOn.AtPtsAlt Q' :=
  Closed.imp h fun Fm _ _ H => by
    obtain ⟨a, ha⟩ := H
    exact ⟨a, fun x hx hle i p hp hm => f Fm x hx i p hm (ha x hx hle i p hp hm)⟩
open Classical in
set_option maxHeartbeats 1600000 in
theorem modelSt_of_small_frame_gal : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.ChebotarevDegreeOne → _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' →
    _root_.GlobalTheory.ExpTie.GaloisStatement → _root_.GlobalTheory.ExpTie.ModelStatement := by
  intro hBS hCheb hS hFr hGal
  refine _root_.GlobalTheory.ExpModel.atPts_mono_of_more (_root_.GlobalTheory.ExpModel.atPts_and2_alt hS (_root_.GlobalTheory.ExpModel.atPts_and2_alt hFr hGal)) ?_
  intro eps Fm x hx i p _ H j P W hD hN w hw hR
  obtain ⟨hs, hf, hg⟩ := H
  have hsm : SmallAt p j P w := hs j P W hD hN w hw hR
  haveI hl : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hsm.1⟩
  obtain ⟨F, R, inc, hFok, ⟨T⟩⟩ := @hf j P W hD hN w hw hR hl
  have hG := @hg j P W hD hN w hw hR hl F R inc hFok T
  have hNr := hN.1.Nr_eq
  have ht := hN.1.t_ge
  have hl2 : Formalism.EigenvalueLevelCeiling.plc w ≠ 2 := by have := hsm.2.1; omega
  obtain ⟨fr, cjj, hlk⟩ := GlobalTheory.T.crystallineLatticeLink_of_blockData hBS _ (AlgebraicClosure (Fm.D x i).host.E) (Formalism.EigenvalueLevelCeiling.plc w) hl2 hsm.2.2.1 _ inc T.half
  obtain ⟨jK, hJ⟩ := GlobalTheory.ExpFrame.levelMap_exists (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam
  obtain ⟨_, _, hH⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam jK hFok hJ (NablaT F.O P.Nr W.lam)
  refine ⟨fr, cjj, {m : MaximalSpectrum F.T // ∃ θ, R.Occurs (subZ p j (p.R.mu w)) θ ∧ F.Over θ m.asIdeal},
    fun m => haveI := m.1.isMaximal.isPrime; F.setting W.lam jK m.1.asIdeal, ?_, ?_⟩
  · exact GlobalTheory.T.maximalIdeals_meeting_subspace_cover _ _ _ (blk p j (p.R.mu w)) w _ P.Nr F W.lam jK hFok hJ hH R (lvlL p) _ hsm.2.2.2.1
  · rintro ⟨m, θ0, hocc, hov⟩
    have hop : ∀ Q, (blk p j (p.R.mu w)).op (Q, 0) = 1 := fun Q => (p.charW.base.fam.degL j (p.R.mu w) Q).1
    obtain ⟨hb, he⟩ := GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part _ _ _ (blk p j (p.R.mu w)) w (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam R _ hop hsm.2.2.2.2 θ0 hocc
    exact ⟨GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok, winputs_frame _ (AlgebraicClosure (Fm.D x i).host.E) hCheb (Formalism.EigenvalueLevelCeiling.plc w) _ inc fr cjj P W hN.2.2.1
      (hlk P W hN.1 hN.2.2.1 hD.box) F hFok R.HasBlock hG jK hJ hH (GlobalTheory.T.finite_frameCoeffRing_quotient_prime _ _ _ F hFok) (GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok) m.asIdeal θ0 he hb hov⟩
end GlobalTheory.ExpModel
end
end
end
end
