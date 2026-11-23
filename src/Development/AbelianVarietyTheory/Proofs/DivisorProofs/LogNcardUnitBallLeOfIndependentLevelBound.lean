module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallLePowMulSmaller

section

@[expose] public section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem finrank_span_finset_le_of_indep {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (T : Finset G) (r : ℕ)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ (T : Set G)) → n ≤ r) :
    Module.finrank ℤ (Submodule.span ℤ (T : Set G)) ≤ r := by
  classical
  haveI : HasUniqueDiv G := IsAddTorsionFree.hasUniqueDiv
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (Subtype.val : ↥(T : Set G) → G)
  have ha : ∀ i : (T : Set G), ∃ a : ℤ, a ≠ 0 ∧ a • (i : G) ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro i
    by_cases h : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, h, rfl⟩⟩
    · exact hmax i h
  choose a ha0 ha using ha
  set M : ℤ := ∏ i, a i with hMdef
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hMmem : ∀ x ∈ Submodule.span ℤ (T : Set G), M • x ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have e : M = a ⟨y, hy⟩ * ∏ i ∈ Finset.univ.erase ⟨y, hy⟩, a i :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
      rw [e, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ha ⟨y, hy⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  let f : Submodule.span ℤ (T : Set G) →ₗ[ℤ] Submodule.span ℤ (Subtype.val '' s) :=
    { toFun := fun x => ⟨M • (x : G), hMmem x x.2⟩
      map_add' := by intro x y; ext; simp [smul_add]
      map_smul' := by
        intro c x; ext
        change M • (c • (x : G)) = c • (M • (x : G))
        exact smul_comm _ _ _ }
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (smul_right_injective G hM0 e)
  have hsfin : (Subtype.val '' s : Set G).Finite := (Set.toFinite s).image _
  haveI : Module.Finite ℤ (Submodule.span ℤ (Subtype.val '' s)) := Module.Finite.span_of_finite ℤ hsfin
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have hli : LinearIndepOn ℤ id (Subtype.val '' s) := hs.id_image
  haveI := hsfin.fintype
  rw [finrank_span_set_eq_card hli, Set.toFinset_card] at h1
  let eqv := Fintype.equivFin (Subtype.val '' s : Set G)
  have h2 := hr _ (fun j => (eqv.symm j : G)) (hli.comp _ eqv.symm.injective) (by
    intro j
    obtain ⟨i, _, hi⟩ := (eqv.symm j).2
    rw [← hi]; exact i.2)
  exact h1.trans h2

theorem encard_finset_le_pow_mul {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G)
    (B : ℝ → Set G) (hB : IsBallFam Λ B) (R : ℝ) (q r : ℕ) (hq : 0 < q)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r)
    (T : Finset G) (hT : (T : Set G) ⊆ B R) :
    (T : Set G).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  classical
  haveI : HasUniqueDiv G := IsAddTorsionFree.hasUniqueDiv
  haveI : NeZero q := ⟨hq.ne'⟩
  set L := Submodule.span ℤ (T : Set G) with hLdef
  have hd : Module.finrank ℤ L ≤ r :=
    finrank_span_finset_le_of_indep T r (fun n e he hmem => hr n e he (fun j => hT (hmem j)))
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set d := Module.finrank ℤ L with hddef
  let b := Module.finBasis ℤ L
  let v : G → (Fin d → ℤ) := fun x => if hx : x ∈ L then b.equivFun ⟨x, hx⟩ else 0
  let c : G → (Fin d → ZMod q) := fun x i => ((v x i : ℤ) : ZMod q)
  let z : G → G → G := fun x y => ((b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) : G)
  have hkey : ∀ x ∈ L, ∀ y ∈ L, c x = c y → q • z x y = x - y := by
    intro x hx y hy hc
    have hdvd : ∀ i, (q : ℤ) ∣ v x i - v y i := by
      intro i
      have e := congrFun hc i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      exact sub_eq_zero.2 e
    have hvx : v x = b.equivFun ⟨x, hx⟩ := dif_pos hx
    have hvy : v y = b.equivFun ⟨y, hy⟩ := dif_pos hy
    have e : q • (b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) = ⟨x, hx⟩ - ⟨y, hy⟩ := by
      apply b.equivFun.injective
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub, ← hvx, ← hvy]
      funext i
      simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul]
      exact Int.mul_ediv_cancel' (hdvd i)
    have e2 := congrArg Subtype.val e
    simpa [z] using e2
  have hLΛ : ∀ x ∈ L, x ∈ Λ := by
    intro x hx
    have : L ≤ Λ.toIntSubmodule := Submodule.span_le.2 (fun y hy => hB.subset R (hT hy))
    exact this hx
  let ρ : (Fin d → ZMod q) → G := Function.invFunOn c (T : Set G)
  have hρ : ∀ x ∈ (T : Set G), ρ (c x) ∈ (T : Set G) ∧ c (ρ (c x)) = c x := fun x hx =>
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  let φ : G → (Fin d → ZMod q) × G := fun x => (c x, z x (ρ (c x)))
  have hsub : ∀ x ∈ (T : Set G), x ∈ L := fun x hx => Submodule.subset_span hx
  have hmaps : Set.MapsTo φ (T : Set G) (Set.univ ×ˢ B (2 * R / q)) := by
    intro x hx
    refine ⟨Set.mem_univ _, ?_⟩
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h2 : x - ρ (c x) ∈ B (R + R) := hB.sub_mem R R _ _ (hT hx) (hT hyT)
    have hqR : ((q : ℝ)) * (2 * R / q) = R + R := by
      have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp; ring
    have hzΛ : z x (ρ (c x)) ∈ Λ := hLΛ _ (Subtype.property _)
    refine (hB.nsmul_iff q (2 * R / q) _ hq hzΛ).1 ?_
    rw [hqR, h1]; exact h2
  have hinj : Set.InjOn φ (T : Set G) := by
    intro x hx x' hx' h
    have hc : c x = c x' := congrArg Prod.fst h
    have hz : z x (ρ (c x)) = z x' (ρ (c x')) := congrArg Prod.snd h
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h1' := hkey x' (hsub x' hx') (ρ (c x)) (hsub _ hyT) (by rw [hyc, hc])
    rw [← hc] at hz
    rw [hz] at h1
    exact sub_left_injective (h1.symm.trans h1')
  have hle := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_prod, Set.encard_univ] at hle
  refine hle.trans ?_
  gcongr
  rw [ENat.card_eq_coe_fintype_card]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact_mod_cast Nat.pow_le_pow_right hq hd

theorem encard_ball_le_pow_mul : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G),
    IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q →
    (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) →
    (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  intro G _ _ Λ B hB R q r hq hr
  by_contra hlt
  push_neg at hlt
  have hC := hlt.ne_top
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hC
  have htfin : t.Finite := Set.encard_ne_top_iff.1 (by rw [htc, ← hm]; exact ENat.coe_ne_top (m + 1))
  have h := encard_finset_le_pow_mul Λ B hB R q r hq hr htfin.toFinset (by simpa using hts)
  rw [Set.Finite.coe_toFinset, htc, ← hm] at h
  norm_cast at h
  omega

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallLePowMulSmallerStatement

section

@[expose] public section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q → (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) → (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  first | exact @GlobalTheory.VolBr.encard_ball_le_pow_mul | exact GlobalTheory.VolBr.encard_ball_le_pow_mul | (intros; apply GlobalTheory.VolBr.encard_ball_le_pow_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentAdaptedToDecreasingChainA

section

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem exists_linearIndependent_finCons_of_lt {G : Type} [AddCommGroup G] {m k : ℕ}
    (e : Fin m → G) (he : LinearIndependent ℤ e) (f : Fin k → G) (hf : LinearIndependent ℤ f)
    (hmk : m < k) : ∃ j, LinearIndependent ℤ (Fin.cons (f j) e : Fin m.succ → G) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hc : ∀ j, ∃ c : ℤ, c ≠ 0 ∧ c • f j ∈ Submodule.span ℤ (Set.range e) := by
    intro j
    by_contra h
    push_neg at h
    apply hcon j
    refine LinearIndependent.finCons' (f j) e he fun c y hy hxy => ?_
    by_contra hc0
    apply h c hc0
    have : c • f j = -y := eq_neg_of_add_eq_zero_left hxy
    rw [this]
    exact Submodule.neg_mem _ hy
  choose c hc0 hcs using hc
  have hg : LinearIndependent ℤ (fun j => c j • f j) := by
    rw [Fintype.linearIndependent_iff] at hf ⊢
    intro a ha j
    have := hf (fun j => a j * c j) (by simpa [mul_smul] using ha) j
    exact (mul_eq_zero.mp this).resolve_right (hc0 j)
  have hle := linearIndependent_le_span_aux' (fun j => c j • f j) hg (Set.range e)
    (by rintro _ ⟨j, rfl⟩; exact hcs j)
  have h2 : Fintype.card (Set.range e) = m := by
    rw [Set.card_range_of_injective he.injective, Fintype.card_fin]
  rw [h2, Fintype.card_fin] at hle
  omega

theorem exists_linearIndependent_extend_with_levels {G : Type} [AddCommGroup G] (S : ℕ → Set G) {k : ℕ} (f : Fin k → G)
    (hf : LinearIndependent ℤ f) (hfS : ∀ j, f j ∈ S 0) (m : ℕ) (e : Fin m → G) (n : Fin m → ℕ)
    (he : LinearIndependent ℤ e) (heS : ∀ j, e j ∈ S (n j)) :
    ∀ k', m ≤ k' → k' ≤ k → ∃ (e2 : Fin k' → G) (n2 : Fin k' → ℕ), LinearIndependent ℤ e2 ∧
      (∀ j, e2 j ∈ S (n2 j)) ∧ ∑ j, n2 j = ∑ j, n j := by
  intro k' hm
  induction k', hm using Nat.le_induction with
  | base => intro _; exact ⟨e, n, he, heS, rfl⟩
  | succ k' hmk ih =>
    intro hk
    obtain ⟨e2, n2, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨j, hj⟩ := exists_linearIndependent_finCons_of_lt e2 h1 f hf (by omega)
    refine ⟨Fin.cons (f j) e2, Fin.cons 0 n2, hj, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hfS j
      · simpa using h2 i
    · rw [Fin.sum_cons, zero_add, h3]

theorem exists_linearIndependent_adapted_to_decreasing_chain : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ),
    (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) →
    (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ),
      LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧
      ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  intro G _ _ S hS N
  induction N generalizing S with
  | zero =>
    intro r hr _
    obtain ⟨e, he, heS⟩ := hr 0
    exact ⟨e, fun _ => 0, he, heS, by simp⟩
  | succ N ih =>
    intro r hr hrd
    obtain ⟨e', n', he', heS', hsum⟩ := ih (fun i => S (i + 1)) (fun i => hS (i + 1))
      (fun i => r (i + 1)) (fun i => hr (i + 1)) (fun i => hrd (i + 1))
    obtain ⟨f, hf, hfS⟩ := hr 0
    obtain ⟨e, n, he, heS, hn⟩ := exists_linearIndependent_extend_with_levels S f hf hfS (r (0 + 1)) e' (fun j => n' j + 1) he'
      heS' (r 0) (hrd 0) le_rfl
    refine ⟨e, n, he, heS, ?_⟩
    rw [Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum hn ⊢
    omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentAdaptedToDecreasingChainAStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ), (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) → (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ), LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧ ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  first | exact @GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | exact GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | (intros; apply GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNcardUnitBallLeOfIndependentLevelBound

section

@[expose] public section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_unit_ball_le_of_indep_bound :
    ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T →
      (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) →
        ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  classical
  intro G _ _ Λ B hB hfin q T hq hT hbound
  set S : ℕ → Set G := fun i => B ((2 / q : ℝ) ^ i) with hS
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hmono := (isBallFam_mono_neg_add G Λ B hB).1
  have hSdec : ∀ i, S (i + 1) ⊆ S i := by
    intro i
    apply hmono
    have h0 : (0 : ℝ) ≤ 2 / q := by positivity
    have h1 : (2 / q : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast (by omega : 2 ≤ q)
    exact pow_le_pow_of_le_one h0 h1 (Nat.le_succ i)
  set K : ℕ := ⌊T⌋₊ with hK

  have hsize : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ K := by
    intro i m e he hmem
    have h := hbound m e (fun _ => i) he hmem
    apply Nat.le_floor
    refine le_trans ?_ h
    have : m ≤ ∑ _j : Fin m, (i + 1) := by simp; exact Nat.le_mul_of_pos_right m (Nat.succ_pos i)
    exact_mod_cast this
  let P : ℕ → ℕ → Prop := fun i m => ∃ e : Fin m → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i
  let r : ℕ → ℕ := fun i => Nat.findGreatest (P i) K
  have hP0 : ∀ i, P i 0 := fun i => ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  have hrspec : ∀ i, P i (r i) := fun i => Nat.findGreatest_spec (Nat.zero_le K) (hP0 i)
  have hrmax : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ r i := by
    intro i m e he hmem
    exact Nat.le_findGreatest (hsize i m e he hmem) ⟨e, he, hmem⟩
  have hrdec : ∀ i, r (i + 1) ≤ r i := by
    intro i
    obtain ⟨e, he, hmem⟩ := hrspec (i + 1)
    exact hrmax i _ e he (fun j => hSdec i (hmem j))

  have hstep : ∀ i, (S i).encard ≤ ((q ^ r i : ℕ) : ℕ∞) * (S (i + 1)).encard := by
    intro i
    have h := GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller G Λ B hB ((2 / q : ℝ) ^ i) q (r i) (by omega)
      (fun n e he hmem => hrmax i n e he hmem)
    have heq : 2 * (2 / q : ℝ) ^ i / q = (2 / q : ℝ) ^ (i + 1) := by
      rw [pow_succ]; ring
    simpa [hS, heq] using h
  have hiter : ∀ k, (S 0).encard ≤ ((q ^ (∑ i ∈ Finset.range k, r i) : ℕ) : ℕ∞) * (S k).encard := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, pow_add, Nat.cast_mul, mul_assoc]
      gcongr
      exact hstep k

  have hSK : S K ⊆ {0} := by
    intro x hx
    by_contra hx0
    have hli : LinearIndependent ℤ (fun _ : Fin 1 => x) := by
      letI : HasUniqueDiv G := ⟨by
        intro n hn a b h
        exact eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all _ _) h⟩
      rw [linearIndependent_unique_iff]; exact hx0
    have h := hbound 1 (fun _ => x) (fun _ => K) hli (fun _ => hx)
    have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
    simp at h
    linarith
  have hSK1 : (S K).encard ≤ 1 := by
    calc (S K).encard ≤ ({0} : Set G).encard := Set.encard_le_encard hSK
      _ = 1 := Set.encard_singleton 0

  obtain ⟨e, n, he, hmem, hsum⟩ := GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' G S hSdec K r hrspec hrdec
  have hM : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ T := by
    have h1 := hbound (r 0) e n he hmem
    have h2 : ∑ i ∈ Finset.range K, r i ≤ ∑ i ∈ Finset.range (K + 1), r i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ K))
    have h3 : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2.trans hsum
    linarith
  set M := ∑ i ∈ Finset.range K, r i with hMdef
  have hS0 : S 0 = B 1 := by simp [hS]
  have hcard : (B 1).encard ≤ ((q ^ M : ℕ) : ℕ∞) := by
    rw [← hS0]
    calc (S 0).encard ≤ ((q ^ M : ℕ) : ℕ∞) * (S K).encard := hiter K
      _ ≤ ((q ^ M : ℕ) : ℕ∞) * 1 := by gcongr
      _ = _ := mul_one _
  have hncard : (B 1).ncard ≤ q ^ M := by
    rw [← hfin.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  rcases Nat.eq_zero_or_pos (B 1).ncard with h0 | hpos
  · rw [h0]; simp; positivity
  · have hpos' : (0 : ℝ) < (B 1).ncard := by exact_mod_cast hpos
    calc Real.log ((B 1).ncard : ℝ) ≤ Real.log ((q ^ M : ℕ) : ℝ) :=
          Real.log_le_log hpos' (by exact_mod_cast hncard)
      _ = M * Real.log q := by rw [Nat.cast_pow, Real.log_pow]
      _ ≤ T * Real.log q := by gcongr
      _ = Real.log q * T := mul_comm _ _

end GlobalTheory.VolBr
end
end
