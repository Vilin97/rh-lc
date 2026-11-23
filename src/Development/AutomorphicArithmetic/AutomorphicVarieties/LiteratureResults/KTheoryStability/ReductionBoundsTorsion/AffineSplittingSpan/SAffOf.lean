module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.InclInj
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.ProdEmbNeOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SAffOfParts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.TransferAlt

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EvCob

section

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral

namespace EvaluationCoboundary

open PositivityTheory.KB

theorem ev_eq {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) z := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem key {G : Type} [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ) (he : Inv (MonoidHom.id G) e)
    (g : Fin (j + 1) → G) :
    dC e (fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) =
      ev (MonoidHom.id G) e 1 (bd G j (Finsupp.single g 1)) := by

  rw [ev_eq, bd, Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum,
  Finsupp.linearCombination_single, dC, Fin.sum_univ_succ]
  simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.succAbove_zero, one_smul,
    Fin.val_zero, pow_zero, one_mul, map_smul, Finsupp.linearCombination_single, Fin.val_succ]
  congr 1
  · have h := he (g 0) fun i => Fin.partialProd (fun i => g i.succ) i
    simp only [MonoidHom.id_apply, smul_eq_mul] at h
    rw [← h]
    congr 1
    funext i
    rw [Fin.partialProd_succ']
    rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fin.partialProd_contractNth]
    rfl

end EvaluationCoboundary

theorem evCob : EvCob := by
  intro G _ j e he z hz
  have h : ∀ w : Chn G (j + 1), ev (MonoidHom.id G) (dC e) 1 w =
      ev (MonoidHom.id G) e 1 (bd G j w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp [ev]
    | add a b ha hb =>
      rw [map_add (f := _), EvaluationCoboundary.ev_eq, map_add (f := _), ← EvaluationCoboundary.ev_eq, ← EvaluationCoboundary.ev_eq, ha, hb,
        EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq e (bd G j b), ← map_add, ← EvaluationCoboundary.ev_eq]
    | single g r =>
      rw [EvaluationCoboundary.ev_eq, Finsupp.linearCombination_single, EvaluationCoboundary.key j e he g,
        ← Finsupp.smul_single_one, map_smul, EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq, map_smul]
      rw [one_smul, ← map_smul, ← map_smul, Finsupp.smul_single_one]
  rw [h, hz]
  simp [ev]

end PositivityTheory.KB.SplitAffineSpectral

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.LcharKerNotFiniteIndex

section

@[expose] public section

noncomputable section

open NumberField InfinitePlace Pointwise

namespace PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem place_pos (v : (𝓞 L)ˣ) (w : InfinitePlace L) : 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) := w.pos_iff.mpr (by simp)

def lchar (a : InfinitePlace L → ℕ) : (𝓞 L)ˣ →* Multiplicative ℝ where
  toFun v := Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))))
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Units.val_mul, map_mul, map_mul, Real.log_mul (place_pos x w).ne' (place_pos y w).ne']
    ring

theorem lchar_eq_one_iff (a : InfinitePlace L → ℕ) (v : (𝓞 L)ˣ) :
    lchar a v = 1 ↔ ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
  have hpos : ∀ w : InfinitePlace L, 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    fun w => pow_pos (place_pos v w) _
  have hP : 0 < ∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    Finset.prod_pos fun w _ => hpos w
  have hlog : Real.log (∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w) =
      ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))) := by
    rw [Real.log_prod (fun w _ => (hpos w).ne')]
    exact Finset.sum_congr rfl fun w _ => Real.log_pow _ _
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L)))) = 1 ↔ _
  rw [ofAdd_eq_one, ← hlog]
  constructor
  · intro h
    rw [← Real.exp_log hP, h, Real.exp_zero]
  · intro h
    rw [h, Real.log_one]

theorem lchar_nontrivial (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ∃ v, lchar a v ≠ 1 := by
  classical
  have hcard : ∑ w, a w < Fintype.card (InfinitePlace L) := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, a w₁ = 0 := by
    by_contra h
    push_neg at h
    have h1 : ∑ _w : InfinitePlace L, 1 ≤ ∑ w, a w :=
      Finset.sum_le_sum fun w _ => Nat.one_le_iff_ne_zero.mpr (h w)
    simp at h1
    omega
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, 0 < a w₂ := by
    by_contra h
    push_neg at h
    have h0 : ∑ w, a w = 0 := Finset.sum_eq_zero fun w _ => by
      have := h w
      omega
    omega
  have hne : w₂ ≠ w₁ := by
    rintro rfl
    omega
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit L w₁
  refine ⟨u, fun h => ?_⟩
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L)))) = 1 at h
  rw [ofAdd_eq_one] at h
  have hlt : ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L))) <
      ∑ _w : InfinitePlace L, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w = w₁
      · subst hw
        simp [hw₁]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hu w hw).le
    · exact ⟨w₂, Finset.mem_univ _,
        mul_neg_of_pos_of_neg (by exact_mod_cast hw₂) (hu w₂ hne)⟩
  rw [Finset.sum_const_zero, h] at hlt
  exact lt_irrefl _ hlt

theorem lchar_ker_not_finiteIndex (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ¬ (lchar a).ker.FiniteIndex := by
  intro hfi
  obtain ⟨v, hv⟩ := lchar_nontrivial hC a ha hm
  apply hv
  have hmem := (lchar a).ker.pow_index_mem v
  rw [MonoidHom.mem_ker, map_pow] at hmem
  have hidx : (lchar a).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h1 : Multiplicative.toAdd (lchar a v ^ (lchar a).ker.index) = 0 := by
    rw [hmem]
    rfl
  rw [toAdd_pow, nsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (by exact_mod_cast h1) hidx
  · exact toAdd_eq_zero.mp h1

end PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

open PositivityTheory.KB.SplitAffineSpectral.unitAtAlt in
theorem PositivityTheory.KB.SplitAffineSpectral.unit : PositivityTheory.KB.SplitAffineSpectral.Unit := by
  unfold PositivityTheory.KB.SplitAffineSpectral.Unit
  intro L _ _ hC m hm
  classical
  by_contra hcon
  push_neg at hcon
  let s : Finset (InfinitePlace L → ℕ) :=
    (Fintype.piFinset fun _ => Finset.range (m + 1)).filter
      fun a => 0 < ∑ w, a w ∧ ∑ w, a w ≤ m
  obtain ⟨k, hk, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover
    (H := fun a => (lchar a).ker) (g := fun _ => 1) (s := s) (by
      ext v
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, one_smul]
      obtain ⟨a, ha0, ham, hprod⟩ := hcon v
      refine ⟨a, ?_, ?_⟩
      · simp only [s, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨fun w => ?_, ha0, ham⟩
        have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
        omega
      · exact (MonoidHom.mem_ker).mpr ((lchar_eq_one_iff a v).mpr hprod))
  simp only [s, Finset.mem_filter] at hk
  exact lchar_ker_not_finiteIndex hC k hk.2.1 (lt_of_le_of_lt hk.2.2 hm) hfi
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanForSubsingleton

section

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

theorem altsum (n : ℕ) : ∑ i : Fin n, (-1 : ℝ) ^ (i : ℕ) = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, ih]
    rcases Nat.even_or_odd n with h | h
    · have h' : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr (h.add_odd (by decide))
      simp [h, h', h.neg_one_pow]
    · have h' : ¬ Even n := Nat.not_even_iff_odd.mpr h
      have h'' : Even (n + 1) := h.add_odd (by decide)
      simp [h', h'', h.neg_one_pow]

theorem spanFor_subsingleton (G : Type) [Group G] [Subsingleton G] : SpanFor G := by
  intro q c hc hd
  obtain ⟨v, hv⟩ : ∃ v, ∀ y, c y = v := ⟨c (fun _ => 1), fun y => congrArg c (Subsingleton.elim _ _)⟩
  rcases Nat.even_or_odd q with hq | hq
  · have h3 : ¬ Even (q + 1 + 2) := by
      rw [Nat.not_even_iff_odd]
      rcases hq with ⟨r, rfl⟩
      exact ⟨r + 1, by ring⟩
    have hd1 := congrFun hd (fun _ => 1)
    simp only [dc, hv, Pi.zero_apply] at hd1
    rw [← Finset.sum_mul, altsum, if_neg h3, one_mul] at hd1
    refine ⟨0, Fin.elim0, Fin.elim0, fun _ => 0, fun _ _ _ => rfl, ?_⟩
    funext y
    simp [dc, hv, hd1]
  · have h2 : ¬ Even (q + 2) := by
      rw [Nat.not_even_iff_odd]
      rcases hq with ⟨r, rfl⟩
      exact ⟨r + 1, by ring⟩
    refine ⟨0, Fin.elim0, Fin.elim0, fun _ => v, fun _ _ _ => rfl, ?_⟩
    funext y
    simp only [dc, hv, Finset.univ_eq_empty, Finset.sum_empty, Pi.add_apply, Pi.zero_apply, zero_add]
    rw [← Finset.sum_mul, altsum, if_neg h2, one_mul]

theorem spanFor_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (hB : SpanFor B) : SpanFor A := by
  intro q c hc hd
  obtain ⟨k, a, α, f, hf, hcf⟩ := hB q (fun z => c (fun j => e.symm (z j)))
    (fun g _ y => by
      simp only [map_mul]
      exact hc _ trivial _)
    (by
      funext z
      have := congrFun hd (fun j => e.symm (z j))
      simpa [dc] using this)
  refine ⟨k, a, fun i j => (α i j).comp (MulEquiv.toAdditive e).toAddMonoidHom, fun y => f (fun j => e (y j)),
    fun g _ y => ?_, ?_⟩
  · simp only [map_mul]
    exact hf _ trivial _
  · funext y
    have := congrFun hcf (fun j => e (y j))
    simp only [MulEquiv.symm_apply_apply] at this
    rw [this]
    simp [Finset.sum_apply, cupH, dc]

def zdata (N : ℕ) : WData (Multiplicative (Fin N → ℤ)) (Multiplicative (Fin (N + 1) → ℤ)) where
  ι := { toFun := fun g => Multiplicative.ofAdd (Fin.cons 0 (Multiplicative.toAdd g))
         map_one' := by
           apply Multiplicative.toAdd.injective; funext i
           refine Fin.cases ?_ (fun j => ?_) i <;> simp
         map_mul' := fun g h => by
           apply Multiplicative.toAdd.injective; funext i
           refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  ρ := { toFun := fun p => Multiplicative.ofAdd (Fin.tail (Multiplicative.toAdd p))
         map_one' := rfl
         map_mul' := fun _ _ => rfl }
  ℓ := { toFun := fun x => (Multiplicative.toAdd (Additive.toMul x)) 0
         map_zero' := rfl
         map_add' := fun _ _ => rfl }
  t := Multiplicative.ofAdd (Fin.cons 1 0)
  ρι := fun _ => rfl
  ρt := rfl
  ℓι := fun g => by simp
  ℓt := by simp
  tc := fun z => mul_comm _ _
  dec := fun p => by
    apply Multiplicative.toAdd.injective; funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
      try rfl

theorem spanFor_pi : ∀ N : ℕ, SpanFor (Multiplicative (Fin N → ℤ))
  | 0 => spanFor_subsingleton _
  | N + 1 => (zdata N).step' (spanFor_pi N)

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

namespace PositivityTheory.KB.SplitAffineSpectral

open PrismSpan

theorem span : Span := by
  intro A _ _ _ q c hc hd
  let e : Multiplicative (Additive A) ≃* Multiplicative (Fin (Module.finrank ℤ (Additive A)) → ℤ) :=
    AddEquiv.toMultiplicative (Module.finBasis ℤ (Additive A)).equivFun.toAddEquiv
  exact spanFor_equiv e (spanFor_pi _) q c hc hd

end PositivityTheory.KB.SplitAffineSpectral

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SAffOf

section

@[expose] public section

namespace PositivityTheory.KB

theorem sAff_of (hCh : SChain) (_hEv : SEv) (hSep : SSep) (_hBr : SBridge) : SAff :=
  SplitAffineSpectral.sAff_of_parts hCh hSep SplitAffineSpectral.core SplitAffineSpectral.transfer SplitAffineSpectral.span SplitAffineSpectral.unit SplitAffineSpectral.eigen
    SplitAffineSpectral.evCob

end PositivityTheory.KB
end
end
