module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDualStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetRepsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSumStatement
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDominantOneAndMul

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem isDominant_one_and_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (J : Subgroup (GL (Fin N) k)) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N),
      IsDominant k N J d hd 1 ∧ ∀ t t' : Levi k (Bl d), IsDominant k N J d hd t →
        IsDominant k N J d hd t' → IsDominant k N J d hd (t * t') := by
  intro k _ _ _ _ N J h d hd
  refine ⟨⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ?_⟩, ?_⟩
  · simpa using hn
  · simpa using hn
  · simpa using hx
  · rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · have key := h1 _ (h1' n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := h2' _ (h2 n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := (h3 _ (h3' x hx).1).1
      convert key using 1
      group
    · have key := (h3' _ (h3 x hx).2).2
      convert key using 1
      group

end GlobalTheory.CompanionTheory.Lbc
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedFirstCondition

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem hecke_dominant_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hIw hpos V _ _ π hπ t t' ht ht' T T' hT hT' v l hl
  obtain ⟨r, hr, x, hxN, hx⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hIw hpos t' ht'
  have hxJ : ∀ i, x i ∈ J := fun i => (hxN i).1
  have hform := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ _ T' hT' r x hr hxJ hx v
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set g := leviEmb k (stdBlocks d hd) t with hg
  set g' := leviEmb k (stdBlocks d hd) t' with hg'
  have hmul : leviEmb k (stdBlocks d hd) (t * t') = g * g' := map_mul _ _ _
  have hterm : ∀ i, l (π g (π (x i * g') (v : V))) = l (π (g * g') (v : V)) := by
    intro i
    have hc : g * x i * g⁻¹ ∈ J := (ht.1 _ (hxN i)).1
    have hfac : g * (x i * g') = (g * x i * g⁻¹) * (g * g') := by group
    have h1 : l (π (g * x i * g⁻¹) (π (g * g') (v : V))) = l (π (g * g') (v : V)) :=
      LinearMap.congr_fun (hl _ hc) _
    rw [← Module.End.mul_apply, ← map_mul, hfac, map_mul, Module.End.mul_apply, h1]
  have hTT : l (((T * T') v : fixed π J) : V) = l (π g ((T' v : fixed π J) : V)) :=
    (hT (T' v) l hl).symm

  rw [hTT, hform, hmul, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Lbc
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedFirstConditionStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.jacquet_fixed_first_condition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | exact GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | (intros; apply GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantContractsUnipotent

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc Topology Filter Matrix

namespace GlobalTheory.CompanionTheory.ExpandN

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem exists_one_add_smul_mem_unipRad {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) (c : k) :
    ∃ v : GL n k, (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1) ∧ v ∈ unipRad k e := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  have hsame : ∀ i j, blk e i = blk e j → (u : Matrix n n k) i j = (1 : Matrix n n k) i j := by
    intro i j hij
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    obtain rfl : a = b := by simpa using hij
    rw [hD a i j, Matrix.one_apply, Matrix.one_apply]
    simp
  set M : Matrix n n k := 1 + c • ((u : Matrix n n k) - 1) with hM
  have hMsame : ∀ i j, blk e i = blk e j → M i j = (1 : Matrix n n k) i j := by
    intro i j hij
    simp [hM, hsame i j hij]
  have hT : M.BlockTriangular (blk e) := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    have h0 : (u : Matrix n n k) i j = 0 := mem_parab.1 hP i j hij
    simp [hM, h0, Matrix.one_apply_ne hne]
  have hdet : M.det = 1 := by
    rw [hT.det_fintype]
    refine Finset.prod_eq_one fun a _ => ?_
    have : M.toSquareBlock (blk e) a = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [Matrix.toSquareBlock_def]
      simp only [Matrix.of_apply]
      rw [hMsame i j (hi.trans hj.symm), Matrix.one_apply, Matrix.one_apply]
      simp
    rw [this, Matrix.det_one]
  obtain ⟨v, hv⟩ : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by simp [hdet])
  refine ⟨v, hv, mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩⟩
  · rw [hv]; exact hT hij
  · rw [hv, hMsame _ _ (by simp), Matrix.one_apply, Matrix.one_apply]
    simp

theorem val_conj_one_add_smul {n : Type} [Fintype n] [DecidableEq n] (G u v : GL n k) (c : k)
    (hv : (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1)) :
    ((G * v * G⁻¹ : GL n k) : Matrix n n k) =
      1 + c • (((G * u * G⁻¹ : GL n k) : Matrix n n k) - 1) := by
  have h1 : (G : Matrix n n k) * ((G⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, hv, mul_add, add_mul, mul_sub, sub_mul, mul_one,
    Matrix.mul_smul, Matrix.smul_mul, h1]

theorem exists_pow_conj_mem_KN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t →
    ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ,
      leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  intro k _ _ _ _ N h d hd J hJo _ _ _ t ht n hn
  obtain ⟨O, hO, hOJ⟩ := (GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isInducing.isOpen_iff.1 hJo
  have memJ : ∀ x : GL (Fin N) k, x ∈ J ↔ (x : Matrix (Fin N) (Fin N) k) ∈ O := by
    intro x
    have : x ∈ (J : Set (GL (Fin N) k)) ↔ x ∈ (fun g : GL (Fin N) k => g.val) ⁻¹' O := by rw [hOJ]
    exact this
  have h1O : (1 : Matrix (Fin N) (Fin N) k) ∈ O := by
    simpa using (memJ 1).1 J.one_mem
  set X : Matrix (Fin N) (Fin N) k := (n : Matrix (Fin N) (Fin N) k) - 1 with hX
  haveI := nhdsNE_zero_neBot (k := k)
  have hcont : Continuous fun c : k => (1 : Matrix (Fin N) (Fin N) k) + c • X :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ c in 𝓝[≠] (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O := by
    have : ∀ᶠ c in 𝓝 (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O :=
      hcont.continuousAt.eventually_mem (hO.mem_nhds (by simpa using h1O))
    exact this.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, hcO, hc0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hc0' : c ≠ 0 := hc0
  obtain ⟨v, hv, hvN⟩ := exists_one_add_smul_mem_unipRad (stdBlocks d hd) hn c
  have hvJ : v ∈ J := (memJ v).2 (by rw [hv]; exact hcO)
  let U : Set (GL (Fin N) k) := (fun g : GL (Fin N) k =>
    (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • ((g : Matrix (Fin N) (Fin N) k) - 1)) ⁻¹' O
  have hU : IsOpen U := by
    refine hO.preimage ?_
    have hs : Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) - 1 :=
      Units.continuous_val.sub continuous_const
    exact continuous_const.add (hs.const_smul c⁻¹)
  have h1U : (1 : GL (Fin N) k) ∈ U := by
    show (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • (((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O
    simpa using h1O
  obtain ⟨j, hj⟩ := ht.2 U hU h1U
  refine ⟨j, ?_⟩
  have hconjAll : ∀ r : ℕ, leviEmb k (stdBlocks d hd) t ^ r * v *
      (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
    intro r
    induction r with
    | zero => simpa only [pow_zero, one_mul, inv_one, mul_one] using
        (show v ∈ KN k N J d hd from Subgroup.mem_inf.2 ⟨hvJ, hvN⟩)
    | succ r ih =>
      simpa only [pow_succ', _root_.mul_inv_rev, mul_assoc] using ht.1.1 _ ih
  set G := leviEmb k (stdBlocks d hd) t ^ j with hG
  have hconj : G * v * G⁻¹ ∈ KN k N J d hd := hconjAll j
  have hmem := hj v (Subgroup.mem_inf.2 ⟨hvJ, hvN⟩)
  have hval := val_conj_one_add_smul G n v c hv
  have hscaled : (1 : Matrix (Fin N) (Fin N) k) +
      c⁻¹ • (((G * v * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) =
      ((G * n * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    rw [hval]
    simp [smul_smul, inv_mul_cancel₀ hc0']
  obtain ⟨w, hw, hwN⟩ := exists_one_add_smul_mem_unipRad (stdBlocks d hd)
    (Subgroup.mem_inf.1 hconj).2 c⁻¹
  have hw_eq : w = G * n * G⁻¹ := by
    apply Units.ext
    exact hw.trans hscaled
  refine Subgroup.mem_inf.2 ⟨(memJ _).2 ?_, hw_eq ▸ hwN⟩
  have hmem' : (1 : Matrix (Fin N) (Fin N) k) +
      c⁻¹ • (((G * v * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O := hmem
  rw [hval] at hmem'
  simpa [smul_smul, inv_mul_cancel₀ hc0'] using hmem'

end GlobalTheory.CompanionTheory.ExpandN
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantContractsUnipotentStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.strictly_dominant_contracts_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ, leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  first | exact @GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | exact GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | (intros; apply GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantHeckeKernel

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem heckeOp_nilpotent_on_ker :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ t ht T hT v hv
  set e := leviEmb k (stdBlocks d hd) with he

  have hdom : ∀ r : ℕ, IsDominant k N J d hd (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (isDominant_one_and_mul k N J h d hd).1
    | succ r ih =>
      rw [pow_succ]
      exact (isDominant_one_and_mul k N J h d hd).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, IsHeckeOp π J (e (t ^ r)) (T ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ T]
      exact GlobalTheory.T.jacquet_fixed_first_condition k N h d hd J hJo hJc hJf hpos V π hπ _ _ (hdom r) ht.1 _ _ ih hT

  have key : ∀ u ∈ twKer π (unipRad k (stdBlocks d hd)) 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l (π (e t ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := GlobalTheory.T.strictly_dominant_contracts_unipotent k N h d hd J hJo hJc hJf hpos t ht (n : GL (Fin N) k) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹ ∈ KN k N J d hd := by
        have := (hdom j).1 _ hR
        rw [map_pow] at this
        convert this using 1
        rw [add_comm R j, pow_add]
        group
        rfl
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π (e t ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π (e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹) (π (e t ^ (R + j)) w)
          = π (e t ^ (R + j)) (π (n : GL (Fin N) k) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add (f := _), map_add (f := _), hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((T ^ R) v : fixed π J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual _ J hJc V π hπ _ ((T ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, map_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Lbc
end
end
