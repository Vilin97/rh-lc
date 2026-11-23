module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConj

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.ParabConj

theorem stdBlocks_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s} (i : Fin (d a)) (j : Fin (d b))
    (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_stdMaxParab_of_le_conjBy (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r) (g : GL (Fin r) F) (H : parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h)) :
    g ∈ stdMaxParab F h := by
  by_contra hg
  have hg' := hg
  rw [mem_stdMaxParab] at hg'
  push Not at hg'
  obtain ⟨q, j, hj, hq, hne⟩ := hg'
  refine hg (inv_mem_iff.1 ((mem_stdMaxParab h).2 fun i p hp hi => ?_))
  have hpq : p < q := by rw [Fin.lt_def]; omega
  let t : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection p q (1 : F))
    (by rw [Matrix.det_transvection_of_ne p q hpq.ne]; exact one_ne_zero)
  have ht : (t : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q 1 := rfl
  have htP : t ∈ parab F (stdBlocks d hd) := by
    refine mem_parab_iff.2 fun x y u v hyx => ?_
    have hlt := stdBlocks_lt d hd u v hyx
    rw [ht, Matrix.add_apply, Matrix.one_apply_ne hlt.ne', zero_add]
    refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨e1, e2⟩
    rw [← e1, ← e2] at hlt
    exact lt_asymm hlt hpq
  have h0 := (mem_stdMaxParab h).1 (mem_conjBy.1 (H htP)) i j hj hi
  have hij : i ≠ j := by rintro rfl; omega
  have hmul : ((g⁻¹ * t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * Matrix.single p q (1 : F) *
        (g : Matrix (Fin r) (Fin r) F) := by
    rw [Units.val_mul, Units.val_mul, ht, mul_add, add_mul, mul_one, Units.inv_mul]
  rw [hmul, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, Matrix.mul_apply,
    Finset.sum_eq_single q (fun x _ hx => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]) (by simp),
    Matrix.mul_single_apply_same, mul_one] at h0
  exact (mul_eq_zero.1 h0).resolve_right hne

end GlobalTheory.ParabConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConjStatement

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r) (g : GL (Fin r) F),
    parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h) → g ∈ stdMaxParab F h := by
  first | exact @GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | exact GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | (intros; apply GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMaxCompactInterConjRadicalContainsConj

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.RadRedLift

theorem exists_lift_unipRad (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (v : GL n 𝓀[k]) (hv : v ∈ unipRad 𝓀[k] e) :
    ∃ w : KO k n, (w : GL n k) ∈ unipRad k e ∧ GlobalTheory.LocGL.redK k n w = v := by
  classical
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) ((v : Matrix n n 𝓀[k]) i j)
  let B : Matrix n n 𝒪[k] := Matrix.of fun i j => if blk e i < blk e j then A i j else (1 : Matrix n n 𝒪[k]) i j
  have h1 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = v := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, B, Matrix.of_apply]
    split_ifs with hij
    · exact hA i j
    · rw [CuspMax.mem_unipRad_iff_entries.1 hv i j hij]
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  have hd : IsUnit B.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1]
    exact (Matrix.GeneralLinearGroup.det v).ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨GlobalTheory.LocGL.toKO k n u, CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_, Units.ext ?_⟩
  · change algebraMap 𝒪[k] k ((u : Matrix n n 𝒪[k]) i j) = _
    rw [hu]
    simp only [B, Matrix.of_apply, if_neg hij, Matrix.one_apply]
    split_ifs <;> simp
  · simp only [GlobalTheory.LocGL.redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [← h1, ← hu]; rfl

theorem red_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {r a b : ℕ} (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  intro k _ _ _ _ r a b h g₀
  obtain ⟨k₀, p, hp, rfl⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r g₀
  let κ : KO k (Fin r) := ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀, k₀, rfl⟩
  have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi => hp (show j < i from by
    rw [Fin.lt_def]; omega)
  refine ⟨GlobalTheory.LocGL.redK k (Fin r) κ, fun v hv => ?_⟩
  obtain ⟨w, hw, rfl⟩ := exists_lift_unipRad k _ v hv
  refine ⟨(κ * w * κ⁻¹ : KO k (Fin r)), (κ * w * κ⁻¹).2, ?_, ?_⟩
  · rw [mem_conjBy]
    have hn := parab_le_normalizer k _ (inv_mem hpP)
    have := (Subgroup.mem_normalizer_iff.1 hn (w : GL (Fin r) k)).1 hw
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ : GL (Fin r) k) * p)⁻¹ *
        ((κ * w * κ⁻¹ : KO k (Fin r)) : GL (Fin r) k) * (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ * p) =
        p⁻¹ * w * p⁻¹⁻¹ := by
      change ((κ : GL (Fin r) k) * p)⁻¹ * ((κ : GL (Fin r) k) * w * (κ : GL (Fin r) k)⁻¹) * ((κ : GL (Fin r) k) * p) = _
      group
    rw [e]
    exact this
  · rw [← map_inv, ← map_mul, ← map_mul]

end GlobalTheory.RadRedLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMaxCompactInterConjRadicalContainsConjStatement

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.reduction_maxCompact_inter_conjRadical_contains_conj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r a b : ℕ}
    (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  first | exact @GlobalTheory.RadRedLift.red_lift | exact GlobalTheory.RadRedLift.red_lift | (intros; apply GlobalTheory.RadRedLift.red_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadicalStatement

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.stdMaxParabolicRadical_le_blockUnipotentRadical : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r),
    parab F (stdBlocks d hd) ≤ stdMaxParab F h → stdMaxRad F h ≤ unipRad F (stdBlocks d hd) := by
  first | exact @GlobalTheory.RadRev.stdMaxRad_le_unipRad | exact GlobalTheory.RadRev.stdMaxRad_le_unipRad | (intros; apply GlobalTheory.RadRev.stdMaxRad_le_unipRad <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanish

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.TypeConstTerm

theorem isClosed_of_isParabRad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    (P N : Subgroup (GL (Fin r) k)), IsParabRad P N → IsClosed (N : Set (GL (Fin r) k)) := by
  intro k _ _ _ _ r P N hPN
  obtain ⟨s, d, hd, g, -, rfl⟩ := hPN
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hU : IsClosed (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) := by
    have : (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : blk (stdBlocks d hd) j < blk (stdBlocks d hd) i),
          {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) i j = 0}) ∩
        ⋂ c, ⋂ i, ⋂ j, {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) (stdBlocks d hd ⟨c, i⟩)
          (stdBlocks d hd ⟨c, j⟩) = (1 : Matrix (Fin (d c)) (Fin (d c)) k) i j} := by
      ext x
      simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ?_ continuous_const) (isClosed_iInter fun c => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq ?_ continuous_const)
    · exact Units.continuous_val.matrix_elem _ _
    · exact Units.continuous_val.matrix_elem _ _
  have : (conjBy g (unipRad k (stdBlocks d hd)) : Set (GL (Fin r) k)) =
      (fun x => g⁻¹ * x * g) ⁻¹' (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) := by
    ext x; exact mem_conjBy
  rw [this]
  exact hU.preimage (by fun_prop)

theorem integral_swap_of_support : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (N : Subgroup G), IsClosed (N : Set G) →
    ∀ (ν : Measure N) [IsFiniteMeasureOnCompacts ν] (Φ : G → G → ℂ), Continuous (Function.uncurry Φ) →
    ∀ (C D : Set G), IsCompact C → IsCompact D → (∀ z u, Φ z u ≠ 0 → z ∈ C ∧ u ∈ D) →
    ∫ u : N, (∫ z, Φ z u ∂μ) ∂ν = ∫ z, (∫ u : N, Φ z u ∂ν) ∂μ := by
  intro G _ _ _ _ _ _ μ _ N hN ν _ Φ hΦ C D hC hD hsupp
  refine (integral_integral_swap_of_hasCompactSupport (f := fun (z : G) (u : N) => Φ z u) (μ := μ) (ν := ν)
    (hΦ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) ?_).symm
  refine HasCompactSupport.intro (hC.prod (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hD)) fun p hp => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := hsupp _ _ hne
  exact hp ⟨h1, h2⟩

theorem integrable_comp_of_SB : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : Subgroup G), IsClosed (N : Set G) → ∀ (ν : Measure N) [IsFiniteMeasureOnCompacts ν] (f : G → ℂ),
    f ∈ SB G → ∀ x y : G, Integrable (fun u : N => f (x * u * y)) ν := by
  intro G _ _ _ _ _ _ N hN ν _ f hf x y
  refine Continuous.integrable_of_hasCompactSupport (hf.1.continuous.comp (by fun_prop)) ?_
  refine HasCompactSupport.intro (hN.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hf.2.isCompact.image (f := fun g => x⁻¹ * g * y⁻¹) (by fun_prop))) fun u hu => ?_
  by_contra hne
  exact hu ⟨x * u * y, subset_tsupport _ hne, by group⟩

theorem conj_stdMaxRad_le (F : Type) [Field F] {r a b : ℕ} (h : a + b = r) (P N : Subgroup (GL (Fin r) F))
    (hPN : IsParabRad P N) (g₀ : GL (Fin r) F) (hP : P ≤ conjBy g₀ (stdMaxParab F h)) :
    conjBy g₀ (stdMaxRad F h) ≤ N := by
  obtain ⟨s, d, hd, g, rfl, rfl⟩ := hPN
  have h1 : parab F (stdBlocks d hd) ≤ conjBy (g⁻¹ * g₀) (stdMaxParab F h) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ conjBy g (parab F (stdBlocks d hd)) := mem_conjBy.2 (by simpa [mul_assoc] using hx)
    have := mem_conjBy.1 (hP hx')
    rw [mem_conjBy]
    simpa [mul_assoc] using this
  have hc := GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj F h d hd _ h1
  have h2 : parab F (stdBlocks d hd) ≤ stdMaxParab F h := by
    intro x hx
    have := mem_conjBy.1 (h1 hx)
    have e : x = (g⁻¹ * g₀) * ((g⁻¹ * g₀)⁻¹ * x * (g⁻¹ * g₀)) * (g⁻¹ * g₀)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hc this) (inv_mem hc)
  have h3 := GlobalTheory.T.stdMaxParabolicRadical_le_blockUnipotentRadical F h d hd h2
  intro y hy
  rw [mem_conjBy] at hy ⊢
  have hn : (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹ ∈ stdMaxRad F h :=
    (Subgroup.mem_normalizer_iff.1 (parab_le_normalizer F _ hc) _).1 hy
  have e : g⁻¹ * y * g = (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹ := by group
  rw [e]
  exact h3 hn

theorem typeConstTermVanish : TypeConstTermVanish := by
  intro k _ _ _ _ r a b h _ _ W _ _ _ τ _ hfix _ _ μ _ φ hφ f hf P N hPN hP ν _ x y
  obtain ⟨g₀, hP⟩ := hP
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hNa := conj_stdMaxRad_le k h P N hPN g₀ hP
  have hNc := isClosed_of_isParabRad k P N hPN
  set e := idemGL k μ τ with he_def
  have key : ∀ x' w : GL (Fin r) k, ∫ u : N, e (x' * u * w) ∂ν = 0 := by
    intro x' w
    obtain ⟨c, hc⟩ := GlobalTheory.T.reduction_maxCompact_inter_conjRadical_contains_conj k h (x' * g₀)
    refine GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero k τ μ N ν (conjBy c (stdMaxRad 𝓀[k] h)) ?_ x' ?_ w
    · intro v hv
      have h0 : τ c⁻¹ v = 0 := hfix _ fun u hu => by
        have := hv (c * u * c⁻¹) (mem_conjBy.2 (by simpa [mul_assoc] using hu))
        calc τ u (τ c⁻¹ v) = τ (u * c⁻¹) v := by rw [map_mul]; rfl
          _ = τ (c⁻¹ * (c * u * c⁻¹)) v := by rw [show u * c⁻¹ = c⁻¹ * (c * u * c⁻¹) by group]
          _ = τ c⁻¹ (τ (c * u * c⁻¹) v) := by rw [map_mul]; rfl
          _ = τ c⁻¹ v := by rw [this]
      have : v = τ c (τ c⁻¹ v) := by rw [← Module.End.mul_apply, ← map_mul]; simp
      rw [this, h0, map_zero]
    · intro v hv
      obtain ⟨u, hu, hu2, hred⟩ := hc _ (mem_conjBy.1 hv)
      refine ⟨x'⁻¹ * u * x', hNa (mem_conjBy.2 ?_), ?_, ?_⟩
      · have := mem_conjBy.1 hu2
        simpa [mul_assoc] using this
      · simpa [mul_assoc] using hu
      · have e1 : x' * (x'⁻¹ * u * x') * x'⁻¹ = u := by group
        have : (⟨x' * (x'⁻¹ * u * x') * x'⁻¹, by rw [e1]; exact hu⟩ : KO k (Fin r)) = ⟨u, hu⟩ := Subtype.ext e1
        rw [this, hred]
        group
  have heSB : e ∈ SB (GL (Fin r) k) :=
    GlobalTheory.Orb.typeIdem_mem_SB μ _ τ GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO
      (by
        have : ((GlobalTheory.LocGL.redK k (Fin r)).ker : Set (KO k (Fin r))) = Subtype.val ⁻¹' (KOne k (Fin r) : Set _) := by
          ext g; exact GlobalTheory.LocGL.redK_eq_one_iff g
        rw [this]; exact GlobalTheory.StepData.isOpen_KOne.preimage continuous_subtype_val)
  have hfSB : f ∈ SB (GL (Fin r) k) := by
    rcases hf with rfl | rfl
    · exact GlobalTheory.Orb.conv_mem_SB heSB hφ
    · exact GlobalTheory.Orb.conv_mem_SB hφ heSB
  refine ⟨integrable_comp_of_SB _ N hNc ν f hfSB x y, ?_⟩
  have hec : Continuous e := heSB.1.continuous
  have hφc : Continuous φ := hφ.1.continuous
  rcases hf with rfl | rfl
  · have h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ e φ (x * u * y) = ∫ z, e (x * u * (y * z)) * φ z⁻¹ ∂μ := by
      intro u
      rw [GlobalTheory.AutomorphicL2Unitary.conv, ← integral_mul_left_eq_self _ (x * u * y)]
      simp [mul_assoc]
    simp_rw [h1]
    rw [integral_swap_of_support _ μ N hNc ν (fun z u => e (x * u * (y * z)) * φ z⁻¹) (by fun_prop) ((fun z : GL (Fin r) k => z⁻¹) '' tsupport φ)
      ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' ((KO k (Fin r) : Set _) ×ˢ tsupport φ))
      (hφ.2.isCompact.image (by fun_prop)) ((GlobalTheory.SplitFlip.isCompact_KO.prod hφ.2.isCompact).image (by fun_prop)) ?_]
    · simp_rw [integral_mul_const]
      simp [key]
    · intro z u hz
      have h1 := left_ne_zero_of_mul hz
      have h2 := subset_tsupport _ (right_ne_zero_of_mul hz)
      refine ⟨⟨z⁻¹, h2, by simp⟩, ⟨(x * u * (y * z), z⁻¹), ⟨?_, h2⟩, by group⟩⟩
      by_contra hK
      exact h1 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)
  · have h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ φ e (x * u * y) = ∫ z, φ z * e (z⁻¹ * x * u * y) ∂μ := by
      intro u
      simp [GlobalTheory.AutomorphicL2Unitary.conv, mul_assoc]
    simp_rw [h1]
    rw [integral_swap_of_support _ μ N hNc ν (fun z u => φ z * e (z⁻¹ * x * u * y)) (by fun_prop) (tsupport φ)
      ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' (tsupport φ ×ˢ (KO k (Fin r) : Set _)))
      hφ.2.isCompact ((hφ.2.isCompact.prod GlobalTheory.SplitFlip.isCompact_KO).image (by fun_prop)) ?_]
    · simp_rw [integral_const_mul]
      simp [key]
    · intro z u hz
      have h1 := subset_tsupport _ (left_ne_zero_of_mul hz)
      have h2 := right_ne_zero_of_mul hz
      refine ⟨h1, ⟨(z, z⁻¹ * x * u * y), ⟨h1, ?_⟩, by group⟩⟩
      by_contra hK
      exact h2 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)

end GlobalTheory.TypeConstTerm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanishStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.typeIdempotent_constantTerm_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish := by
  first | exact @GlobalTheory.TypeConstTerm.typeConstTermVanish | exact GlobalTheory.TypeConstTerm.typeConstTermVanish | (intros; apply GlobalTheory.TypeConstTerm.typeConstTermVanish <;> assumption)
end
end
