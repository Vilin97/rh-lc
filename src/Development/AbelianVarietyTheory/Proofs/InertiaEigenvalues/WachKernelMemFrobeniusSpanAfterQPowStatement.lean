module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFrobeniusFlatCrystalline

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiFlat

section Generic

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
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem span_φ (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) = ⊤ := by
  set S := Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) with hS
  have hA : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤ S.restrictScalars (LetA O n) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y = ∑ m, bN.repr ⟨y, hy⟩ m • (bN m : W.DD T) := by
      have h0 := congrArg Subtype.val (bN.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm

    rw [hy', map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [φD_smulA, ← algebraMap_smul W.EE, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self m))
  have hb : ∀ j, (bN j : W.DD T) ∈ S := by
    intro j
    obtain ⟨k, hk⟩ := W.N_φinv T (bN j) (bN j).2
    change W.Q ^ k • (bN j : W.DD T) ∈ _ at hk
    have h1 := hA hk
    rw [Submodule.restrictScalars_mem] at h1
    obtain ⟨u, hu⟩ := hQ.pow k
    have h2 : (bN j : W.DD T) = ((u⁻¹ : W.EEˣ) : W.EE) • (W.Q ^ k • (bN j : W.DD T)) := by
      rw [← algebraMap_smul W.EE (W.Q ^ k), smul_smul, map_pow, ← hu, Units.inv_mul, one_smul]
    rw [h2]
    exact S.smul_mem _ h1
  let bD : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hT).basis bN
  have hbD : ∀ j, bD j = (bN j : W.DD T) := fun j => by simp [bD, IsBaseChange.basis_apply]
  rw [eq_top_iff, ← bD.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [hbD]
  exact hb j

theorem phi_flat (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q))
    [Nontrivial W.EE] (hr : Module.finrank W.EE (W.DD T) = r) (l : ℕ)
    (hφ₀ : ∀ w : Fin l → PowerSeries O, ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * W.φ₀ (w j) = 0 → w = 0)
    (z : Fin l → W.DD T) (hz : ∀ j, z j ∈ W.N T)
    (hsum : ∑ j : Fin l, (fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) : LetA O n) • W.φD T (z j) = 0) :
    ∀ j, z j = 0 := by
  have hsp := span_φ W T hT bN hQ
  let c : Module.Basis (Fin r) W.EE (W.DD T) :=
    basisOfTopLeSpanOfCardEqFinrank (fun j => W.φD T (bN j)) hsp.ge (by rw [hr, Fintype.card_fin])
  have hli : LinearIndependent W.EE (fun j => W.φD T (bN j)) := by
    have := c.linearIndependent
    rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at this
  set a : Fin l → Fin r → LetA O n := fun j m => bN.repr ⟨z j, hz j⟩ m with ha
  have hzj : ∀ j, z j = ∑ m, a j m • (bN m : W.DD T) := by
    intro j
    have h0 := congrArg Subtype.val (bN.sum_repr ⟨z j, hz j⟩)
    rw [Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    exact h0.symm
  set e : Fin l → LetA O n := fun j => fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) with he
  have hexp : ∑ m, algebraMap (LetA O n) W.EE (∑ j, e j * W.φA (a j m)) • W.φD T (bN m) = 0 := by
    rw [← hsum]

    simp_rw [algebraMap_smul, hzj, map_sum, φD_smulA, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : ∀ m, ∑ j, e j * W.φA (a j m) = 0 := by
    intro m
    have := Fintype.linearIndependent_iff.1 hli _ hexp m
    exact W.EE_inj (by rw [this, map_zero])
  have hzero : ∀ j m, a j m = 0 := by
    intro j m
    funext k
    have h1 := congrFun (hc m) (k + 1)
    simp only [Finset.sum_apply, Pi.mul_apply, he, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply,
      Pi.evalAlgHom_apply, add_sub_cancel_right, Pi.zero_apply] at h1
    exact congrFun (hφ₀ (fun j => a j m k) h1) j
  intro j
  rw [hzj j]
  simp [hzero]

end Generic

end GlobalTheory.NL.PhiFlat

namespace GlobalTheory.NL.PhiFlat



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ z : Fin l → W.DD T, (∀ j, z j ∈ W.N T) → ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) • W.φD T (z j) = 0 → ∀ j, z j = 0 := by
  intro D HW F l _ K s LL h W T hT z hz hsum
  obtain ⟨bN⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hQ : IsUnit (algebraMap (AA K LL) W.EE W.Q) := by
    have := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    rw [pow_zero, AlgHom.one_apply] at this
    exact this
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcpl, hnu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  haveI : Nontrivial W.EE :=
    ⟨⟨algebraMap (AA K LL) W.EE 0, algebraMap (AA K LL) W.EE 1, fun h0 => zero_ne_one (W.EE_inj h0)⟩⟩
  refine GlobalTheory.NL.PhiFlat.phi_flat W T hT bN hQ (W.DD_free T).2 l ?_ z hz hsum
  intro w hw
  obtain ⟨y, -, huniq⟩ := GlobalTheory.Cyc.phi_free l (↥(OL LL)) hl0 hnu 0
  rw [hφ] at hw
  have e1 := huniq w hw.symm
  have e2 := huniq 0 (by simp)
  rw [e1, e2]

end GlobalTheory.NL.PhiFlat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFrobeniusFlatCrystallineStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachFrobenius_flat_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ z : Fin l → W.DD T, (∀ j, z j ∈ W.N T) → ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) • W.φD T (z j) = 0 → ∀ j, z j = 0 :=
  @GlobalTheory.NL.PhiFlat.main
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLetterRingFrobeniusDecomposition

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiDec

theorem phi_dec : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  intro D HW l _ K s LL h W a
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  choose z hz using fun i : Let K => (GlobalTheory.Cyc.phi_free l ↥(OL LL) hl0 hlu (a i)).exists
  refine ⟨fun j i => z (i + 1) j, ?_⟩
  funext i
  rw [Finset.sum_apply]
  have hi : a i = a (i - 1 + 1) := by rw [sub_add_cancel]
  rw [hi, hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  show _ = _ * ((HW l).W K s LL h).φ₀ _
  rw [hφ]

end GlobalTheory.NL.PhiDec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLetterRingFrobeniusDecompositionStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachLetterRing_frobenius_decomposition : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  first | exact @GlobalTheory.NL.PhiDec.phi_dec | exact GlobalTheory.NL.PhiDec.phi_dec | (intros; apply GlobalTheory.NL.PhiDec.phi_dec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelMemFrobeniusSpanAfterQPow

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiSpanKer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA' (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have h := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at h
  exact h

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

variable {m : ℕ} (u : Fin m → LetA O n)

theorem mem_sum_form (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T))
    (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {w : W.DD T} (hw : w ∈ φspan W T S) :
    ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j) := by
  have hadd : ∀ w w' : W.DD T,
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j)) →
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w' = ∑ j, u j • W.φD T (z j)) →
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w + w' = ∑ j, u j • W.φD T (z j) := by
    rintro w w' ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    refine ⟨z + z', fun j => S.add_mem (hz j) (hz' j), ?_⟩
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  have key : ∀ w ∈ φspan W T S, ∀ a : LetA O n,
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ a • w = ∑ j, u j • W.φD T (z j) := by
    intro w hw
    unfold φspan at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      intro a
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hdec a
      refine ⟨fun j => c j • y, fun j => S.smul_mem _ hy, ?_⟩
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [φD_smulA', mul_smul]
    | zero => intro a; exact ⟨0, fun j => S.zero_mem, by simp⟩
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact hadd _ _ (hx a) (hy a)
    | smul b x _ hx => intro a; rw [smul_smul]; exact hx (a * b)
  simpa using key w hw 1

theorem phispan_of (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hinj : Function.Injective (W.map ι)) (hex : Function.Exact (W.map ι) (W.map π))
    (hπN : ∀ x ∈ W.N T₁, W.map π x ∈ W.N T₂)
    (hind : ∀ z : Fin m → W.DD T₂, (∀ j, z j ∈ W.N T₂) →
      ∑ j, u j • W.φD T₂ (z j) = 0 → ∀ j, z j = 0) :
    ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)),
      ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (LetA O n))) := by
  intro y hy
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy
  obtain ⟨k, hk⟩ := W.N_φinv T₁ _ hy
  refine ⟨k, ?_⟩
  have hk' : W.Q ^ k • W.map ι y ∈ φspan W T₁ (W.N T₁) := hk
  obtain ⟨w, hw, he⟩ := mem_sum_form W u T₁ (W.N T₁) hdec hk'
  have hπ0 : ∀ j, W.map π (w j) = 0 := by
    refine hind _ (fun j => hπN _ (hw j)) ?_
    have h1 := congrArg (W.map π) he

    rw [map_smulA, (hex _).2 ⟨y, rfl⟩, smul_zero, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ]
  choose w' hw' using fun j => (hex (w j)).1 (hπ0 j)
  have hmem : ∀ j, w' j ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)) := by
    intro j
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hw']
    exact hw j
  have heq : W.Q ^ k • y = ∑ j, u j • W.φD T₀ (w' j) := by
    apply hinj

    rw [map_smulA, he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ, hw']
  rw [heq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w' j, hmem j, rfl⟩)

end Generic

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π c0 c1 c2 hses
  have hex : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
    let E := ((F l).E K s LL h).tie
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
    refine GlobalTheory.EtaleExact.exact_of_tie E (GlobalTheory.EtaleExact.map_ne_top_of_tie E ?_ ?_) T₀ T₁ T₂ ι π hses
    · rw [hp]
      exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
    · rw [hp]
      exact GlobalTheory.EtaleExact.sep_RW LL
  exact phispan_of W (fun j : Fin l => (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL))
    (GlobalTheory.T.wachLetterRing_frobenius_decomposition D HW l K s LL h) ι π hex.1 hex.2.1 (fun x hx => W.map_N π c1 c2 x hx)
    (GlobalTheory.T.wachFrobenius_flat_crystalline D HW F l K s LL h T₂ c2)

end GlobalTheory.NL.PhiSpanKer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelMemFrobeniusSpanAfterQPowStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  first | exact @GlobalTheory.NL.PhiSpanKer.main | exact GlobalTheory.NL.PhiSpanKer.main | (intros; apply GlobalTheory.NL.PhiSpanKer.main <;> assumption)
end
end
