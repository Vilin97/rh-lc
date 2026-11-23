module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.CbIsChainApply
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linter.Style
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChainsOfRange

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.JordanChain

open Module Submodule

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def chainVec (f : V →ₗ[K] V) {ι : Type} (e : ι → ℕ) (v : ι → V) : (Σ a, Fin (e a)) → V :=
  fun p => (f ^ (p.2 : ℕ)) (v p.1)

theorem pow_coe_of_restrict {W : Submodule K V} (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hg : ∀ x, (g x : V) = f x) (k : ℕ) (x : W) : (((g ^ k) x : W) : V) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hg]

theorem exists_chains_of_range [FiniteDimensional K V] (f : V →ₗ[K] V)
    (g : LinearMap.range f →ₗ[K] LinearMap.range f) (hg : ∀ x, (g x : V) = f x)
    {ι' : Type} [Fintype ι'] (e' : ι' → ℕ) (he' : ∀ b, 0 < e' b) (w : ι' → LinearMap.range f)
    (h0 : ∀ b, (g ^ e' b) (w b) = 0) (hli : LinearIndependent K (chainVec g e' w))
    (hsp : span K (Set.range (chainVec g e' w)) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  classical
  have hu : ∀ b, ∃ u, f u = (w b : V) := fun b => (w b).2
  choose u hu using hu
  have hstep : ∀ (b : ι') (j : ℕ), (f ^ (j + 1)) (u b) = (f ^ j) (w b : V) := by
    intro b j
    rw [pow_succ, Module.End.mul_apply, hu]
  set N := LinearMap.ker f with hN
  let t : ι' → V := fun b => (f ^ e' b) (u b)
  have htN : ∀ b, t b ∈ N := by
    intro b
    have h1 : f (t b) = (f ^ (e' b + 1)) (u b) := by
      simp only [t]
      rw [pow_succ', Module.End.mul_apply]
    rw [hN, LinearMap.mem_ker, h1, hstep, ← pow_coe_of_restrict f g hg, h0]
    rfl
  have hLV : LinearIndependent K (fun p => ((chainVec g e' w p : LinearMap.range f) : V)) :=
    hli.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  let idx : ι' → Σ b, Fin (e' b) := fun b => ⟨b, ⟨e' b - 1, by have := he' b; omega⟩⟩
  have hidx : Function.Injective idx := fun a b h => congrArg Sigma.fst h
  have ht : LinearIndependent K t := by
    have h2 := hLV.comp idx hidx
    convert h2 using 1
    funext b
    change (f ^ e' b) (u b) = ((g ^ (e' b - 1)) (w b) : LinearMap.range f)
    rw [pow_coe_of_restrict f g hg, ← hstep]
    congr 2
    have := he' b
    omega
  let tN : ι' → N := fun b => ⟨t b, htN b⟩
  have htNli : LinearIndependent K tN := LinearIndependent.of_comp N.subtype ht
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (span K (Set.range tN))
  let bC := Module.finBasis K C
  let z : Fin (finrank K C) → V := fun c => ((bC c : C) : N)
  have hz : ∀ c, f (z c) = 0 := fun c => ((bC c : C) : N).2
  let e : ι' ⊕ Fin (finrank K C) → ℕ := Sum.elim (fun b => e' b + 1) (fun _ => 1)
  let v : ι' ⊕ Fin (finrank K C) → V := Sum.elim u z
  let T := span K (Set.range (chainVec f e v))
  have hTu : ∀ (b : ι') (j : ℕ), j ≤ e' b → (f ^ j) (u b) ∈ T := by
    intro b j hj
    exact subset_span ⟨⟨Sum.inl b, ⟨j, Nat.lt_succ_of_le hj⟩⟩, rfl⟩
  have hTz : ∀ c, z c ∈ T := by
    intro c
    exact subset_span ⟨⟨Sum.inr c, ⟨0, Nat.one_pos⟩⟩, by simp [chainVec, v]⟩
  have hkerS : map N.subtype (span K (Set.range tN)) ≤ T := by
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨b, rfl⟩
    exact hTu b _ le_rfl
  have hkerC : map (N.subtype ∘ₗ C.subtype) ⊤ ≤ T := by
    rw [← bC.span_eq]
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact hTz c
  have hker : N ≤ T := by
    intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ span K (Set.range tN) ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.1 hx'
    have hxe : x = (s : V) + (c : V) := by
      have := congrArg Subtype.val hsc
      simpa using this.symm
    rw [hxe]
    exact T.add_mem (hkerS ⟨s, hs, rfl⟩) (hkerC ⟨⟨c, hc⟩, trivial, rfl⟩)
  have hrange : ∀ y : LinearMap.range f, ∃ x ∈ T, f x = y := by
    have h3 : map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) ≤ map f T := by
      refine (Submodule.map_span_le _ _ _).2 ?_
      rintro _ ⟨⟨b, j⟩, rfl⟩
      refine ⟨(f ^ (j : ℕ)) (u b), hTu b _ j.2.le, ?_⟩
      simp only [chainVec, Submodule.subtype_apply]
      rw [pow_coe_of_restrict f g hg, ← hstep, pow_succ']
      rfl
    intro y
    have hy : (y : V) ∈ map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) := by
      rw [hsp]
      exact ⟨y, trivial, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h3 hy
    exact ⟨x, hx, hxy⟩
  have hTtop : T = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨x', hx', hxx⟩ := hrange ⟨f x, x, rfl⟩
    have hk : x - x' ∈ N := by
      rw [hN, LinearMap.mem_ker, map_sub, hxx]
      simp
    have := T.add_mem (hker hk) hx'
    simpa using this
  have hcard₁ : finrank K (LinearMap.range f) = ∑ b, e' b := by
    have h4 := finrank_span_eq_card hli
    rw [hsp, finrank_top] at h4
    rw [h4, Fintype.card_sigma]
    simp
  have hcard₂ : finrank K N = Fintype.card ι' + finrank K C := by
    have h5 := Submodule.finrank_add_eq_of_isCompl hC
    rw [finrank_span_eq_card htNli] at h5
    exact h5.symm
  have hcard : Fintype.card (Σ a, Fin (e a)) = finrank K V := by
    have h6 := LinearMap.finrank_range_add_finrank_ker f
    rw [Fintype.card_sigma, ← h6, hcard₁, ← hN, hcard₂]
    simp [e, Fintype.sum_sum_type, Finset.sum_add_distrib]
    omega
  refine ⟨ι' ⊕ Fin (finrank K C), inferInstance, e, v, ?_, ?_, ?_, hTtop⟩
  · rintro (b | c)
    · exact Nat.succ_pos _
    · exact Nat.one_pos
  · rintro (b | c)
    · change (f ^ (e' b + 1)) (u b) = 0
      rw [hstep, ← pow_coe_of_restrict f g hg, h0]
      rfl
    · change (f ^ 1) (z c) = 0
      simpa using hz c
  · exact linearIndependent_of_top_le_span_of_card_eq_finrank hTtop.ge hcard

theorem exists_chains : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V), finrank K V = n → IsNilpotent f →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ f hn hf
    by_cases hV : Subsingleton V
    · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun a => a.elim, fun a => a.elim,
        ?_, Subsingleton.elim _ _⟩
      exact linearIndependent_empty_type
    · have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.1 hV
      obtain ⟨m, hm⟩ := hf
      have hlt : finrank K (LinearMap.range f) < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro htop
        have hsurj : Function.Surjective f := LinearMap.range_eq_top.1 htop
        have hs : Function.Surjective (f ^ m) := by
          rw [Module.End.coe_pow]
          exact hsurj.iterate m
        rw [hm] at hs
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        obtain ⟨y, hy⟩ := hs x
        exact hx (by simpa using hy.symm)
      let g : LinearMap.range f →ₗ[K] LinearMap.range f :=
        f.restrict (fun x _ => LinearMap.mem_range_self f x)
      have hg : ∀ x, (g x : V) = f x := fun x => rfl
      have hgn : IsNilpotent g := by
        refine ⟨m, LinearMap.ext fun x => Subtype.ext ?_⟩
        rw [pow_coe_of_restrict f g hg, hm]
        rfl
      obtain ⟨ι', _, e', w, he', h0, hli, hsp⟩ := ih _ hlt (LinearMap.range f) g rfl hgn
      exact exists_chains_of_range f g hg e' he' w h0 hli hsp

theorem exists_chain_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧
      LinearIndependent K (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1)) ∧
      span K (Set.range (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1))) = ⊤ :=
  exists_chains _ V f rfl hf

end GlobalTheory.CompanionTheory.JordanChain
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.CbExistsChainOfGen

section

@[expose] public section

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem cb_exists_chain_of_gen (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (y : ι → W)
    (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (hy : ∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) :
    ∃ B : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B ∧ ∀ p, B p = cbFam N l y p := by
  set S := span E (Set.range (cbFam N l y)) with hSdef
  have hS : ∀ x ∈ S, N x ∈ S := by
    intro x hx
    have : S ≤ S.comap N := by
      rw [hSdef, span_le]
      rintro _ ⟨p, rfl⟩
      show N (cbFam N l y p) ∈ S
      simp only [cbFam]
      rw [cb_pow_succ]
      by_cases h : (p.2 : ℕ) + 1 < l p.1
      · exact subset_span ⟨⟨p.1, ⟨p.2 + 1, h⟩⟩, rfl⟩
      · rw [cb_pow_zero_of_le N (hy0 p.1) (by omega)]; exact S.zero_mem
    exact this hx
  have htop : S ⊔ LinearMap.range N = ⊤ := by
    rw [eq_top_iff, ← B0.span_eq, span_le]
    rintro _ ⟨⟨a, ⟨i, hi⟩⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; exact hy a
    · apply Submodule.mem_sup_right
      rw [cb_isChain_apply N hB0 a (hl a) i hi]
      refine ⟨(N ^ (i - 1)) (B0 ⟨a, ⟨0, hl a⟩⟩), ?_⟩
      rw [cb_pow_succ, show i - 1 + 1 = i by omega]
  have hST : S = ⊤ := cb_eq_top N hN S hS htop
  have hli : LinearIndependent E (cbFam N l y) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [← hSdef, hST])
      (by rw [Module.finrank_eq_card_basis B0])
  refine ⟨Basis.mk hli (by rw [← hSdef, hST]), ?_, fun p => by simp⟩
  exact cb_isChain_of_fam N l y hy0 _ (fun p => by simp)

theorem cb_single (N : W →ₗ[E] W) (L : ℕ) (u : W) (hu : (N ^ L) u = 0) (c : Fin L → E) :
    ∃ s ≤ L, ∃ y : W, (N ^ L) y = 0 ∧ (N ^ s) y = ∑ i, c i • (N ^ (i : ℕ)) u ∧
      u ∈ span E {y} ⊔ LinearMap.range N := by
  classical
  by_cases h : ∃ i, ∃ hi : i < L, c ⟨i, hi⟩ ≠ 0
  · obtain ⟨s, ⟨hsL, hcs⟩, hmin⟩ : ∃ s, (∃ hi : s < L, c ⟨s, hi⟩ ≠ 0) ∧
        ∀ i < s, ∀ hi : i < L, c ⟨i, hi⟩ = 0 :=
      ⟨Nat.find h, Nat.find_spec h, fun i hi hiL => by
        by_contra hne; exact Nat.find_min h hi ⟨hiL, hne⟩⟩
    set y : W := ∑ i : Fin L, if s ≤ (i : ℕ) then c i • (N ^ ((i : ℕ) - s)) u else 0 with hydef
    set z : W := ∑ i : Fin L, if s < (i : ℕ) then c i • (N ^ ((i : ℕ) - s - 1)) u else 0 with hzdef
    refine ⟨s, hsL.le, y, ?_, ?_, ?_⟩

    · rw [hydef, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs
      · rw [map_smul, cb_pow_pow, cb_pow_zero_of_le N hu (by omega), smul_zero]
      · exact map_zero _

    · rw [hydef, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h1
      · rw [map_smul, cb_pow_pow, show s + ((i : ℕ) - s) = i by omega]
      · rw [map_zero, hmin i (by omega) i.2, zero_smul]
    · have hyz : y = c ⟨s, hsL⟩ • u + N z := by
        have hc : c ⟨s, hsL⟩ • u = ∑ i : Fin L, if i = ⟨s, hsL⟩ then c i • u else 0 := by
          rw [Finset.sum_ite_eq']; simp

        rw [hc, hydef, hzdef, map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases lt_trichotomy (i : ℕ) s with h1 | h1 | h1
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_neg (by omega), if_neg hne, if_neg (by omega), map_zero, add_zero]
        · have he : i = ⟨s, hsL⟩ := Fin.ext h1
          rw [if_pos (by omega), if_pos he, if_neg (by omega), map_zero, add_zero, h1, Nat.sub_self,
            pow_zero, Module.End.one_apply]
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_pos (by omega), if_neg hne, if_pos h1, zero_add, map_smul, cb_pow_succ,
            show (i : ℕ) - s - 1 + 1 = (i : ℕ) - s by omega]
      have hu_eq : u = (c ⟨s, hsL⟩)⁻¹ • y - N ((c ⟨s, hsL⟩)⁻¹ • z) := by
        rw [hyz, smul_add, smul_smul, inv_mul_cancel₀ hcs, one_smul, map_smul]; abel
      rw [hu_eq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self y))) (Submodule.mem_sup_right (LinearMap.mem_range_self N _))
  · push Not at h
    refine ⟨L, le_rfl, u, hu, ?_, Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)⟩
    rw [hu]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show c i = 0 from h i i.2, zero_smul]

theorem cb_init (N : W →ₗ[E] W) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (v : W) :
    ∃ (y : ι → W) (s : ι → ℕ), (∀ a, (N ^ l a) (y a) = 0) ∧
      (∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) ∧
      (∀ a, s a ≤ l a) ∧ v = ∑ a, (N ^ s a) (y a) := by
  have H : ∀ a, ∃ s ≤ l a, ∃ y : W, (N ^ l a) y = 0 ∧
      (N ^ s) y = ∑ i : Fin (l a), B0.repr v ⟨a, i⟩ • (N ^ (i : ℕ)) (B0 ⟨a, ⟨0, hl a⟩⟩) ∧
      B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E {y} ⊔ LinearMap.range N :=
    fun a => cb_single N (l a) _ (cb_isChain_len N hB0 a (hl a)) _
  choose s hs y hy0 hys hyu using H
  refine ⟨y, s, hy0, fun a => ?_, hs, ?_⟩
  · have hle : span E {y a} ≤ span E (Set.range (cbFam N l y)) := by
      rw [span_le, Set.singleton_subset_iff]
      exact subset_span ⟨⟨a, ⟨0, hl a⟩⟩, by simp [cbFam]⟩
    exact sup_le_sup_right hle _ (hyu a)
  · conv_lhs => rw [← B0.sum_repr v]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hys]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cb_isChain_apply' N hB0 a (hl a) i]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainB

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem cb_step (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] [DecidableEq ι] {l : ι → ℕ}
    (hl : ∀ a, 0 < l a) (v : W) (y : ι → W) (s : ι → ℕ) (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (hBy : ∀ p, B p = cbFam N l y p)
    (hs : ∀ a, s a ≤ l a) (hv : v = ∑ a, (N ^ s a) (y a)) (a b : ι) (hab : s b + (l a - l b) < s a) :
    ∃ (y' : ι → W) (s' : ι → ℕ), (∀ a, (N ^ l a) (y' a) = 0) ∧
      (∃ B' : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B' ∧ ∀ p, B' p = cbFam N l y' p) ∧
      (∀ a, s' a ≤ l a) ∧ v = ∑ a, (N ^ s' a) (y' a) ∧ ∑ a, s' a < ∑ a, s a := by
  have hne : a ≠ b := by rintro rfl; simp at hab
  set i0 := l a - l b with hi0
  set d := s a - (s b + i0) with hd
  have hdpos : 0 < d := by omega
  set y' : ι → W := Function.update (Function.update y b (y b - (N ^ i0) (y a))) a
    (y a + (N ^ d) (y a)) with hy'
  set s' : ι → ℕ := Function.update s a (s b + i0) with hs'
  have y'a : y' a = y a + (N ^ d) (y a) := by simp [y']
  have y'b : y' b = y b - (N ^ i0) (y a) := by simp [y', hne.symm]
  have y'c : ∀ c, c ≠ a → c ≠ b → y' c = y c := by intro c h1 h2; simp [y', h1, h2]
  have s'a : s' a = s b + i0 := by simp [s']
  have s'c : ∀ c, c ≠ a → s' c = s c := by intro c h; simp [s', h]
  have hy0' : ∀ c, (N ^ l c) (y' c) = 0 := by
    intro c
    by_cases hca : c = a
    · rw [hca, y'a, map_add (f := _), hy0, cb_pow_pow, cb_pow_zero_of_le N (hy0 a) (by omega), add_zero]
    by_cases hcb : c = b
    · rw [hcb, y'b, map_sub, hy0, cb_pow_pow, cb_pow_zero_of_le N (hy0 a) (by omega), sub_zero]
    · rw [y'c c hca hcb, hy0]
  have hgen : ∀ c, B ⟨c, ⟨0, hl c⟩⟩ ∈ span E (Set.range (cbFam N l y')) ⊔ LinearMap.range N := by
    set T := span E (Set.range (cbFam N l y')) ⊔ LinearMap.range N with hT
    have hmemS : ∀ c, y' c ∈ T := fun c =>
      Submodule.mem_sup_left (subset_span ⟨⟨c, ⟨0, hl c⟩⟩, by simp [cbFam]⟩)
    have hmemR : ∀ j x, 0 < j → (N ^ j) x ∈ T := fun j x hj =>
      Submodule.mem_sup_right ⟨(N ^ (j - 1)) x, by rw [cb_pow_succ, show j - 1 + 1 = j by omega]⟩
    have hya : y a ∈ T := by
      have : y a = y' a - (N ^ d) (y a) := by rw [y'a]; abel
      rw [this]; exact T.sub_mem (hmemS a) (hmemR d _ hdpos)
    have hyb : y b ∈ T := by
      have : y b = y' b + (N ^ i0) (y a) := by rw [y'b]; abel
      rw [this]; refine T.add_mem (hmemS b) ?_
      rcases Nat.eq_zero_or_pos i0 with h | h
      · rw [h, pow_zero, Module.End.one_apply]; exact hya
      · exact hmemR i0 _ h
    intro c
    have hc : B ⟨c, ⟨0, hl c⟩⟩ = y c := by rw [hBy]; simp [cbFam]
    rw [hc]
    by_cases hca : c = a
    · rw [hca]; exact hya
    by_cases hcb : c = b
    · rw [hcb]; exact hyb
    rw [← y'c c hca hcb]; exact hmemS c
  obtain ⟨B', hB', hB'y⟩ := cb_exists_chain_of_gen N hN B hB hl y' hy0' hgen
  have hsle : ∀ c, s' c ≤ l c := by
    intro c
    by_cases hca : c = a
    · rw [hca, s'a]; have := hs a; omega
    · rw [s'c c hca]; exact hs c
  have hterm : ∀ c, (N ^ s' c) (y' c) = (N ^ s c) (y c) +
      ((if c = a then (N ^ (s b + i0)) (y a) else 0) - (if c = b then (N ^ (s b + i0)) (y a) else 0)) := by
    intro c
    by_cases hca : c = a
    · rw [hca, s'a, y'a, if_pos rfl, if_neg hne, map_add (f := _), cb_pow_pow, show s b + i0 + d = s a by omega]
      abel
    by_cases hcb : c = b
    · rw [hcb, s'c b (fun h => hne h.symm), y'b, if_neg (fun h => hne h.symm), if_pos rfl, map_sub, cb_pow_pow]
      abel
    · rw [s'c c hca, y'c c hca hcb, if_neg hca, if_neg hcb, sub_zero, add_zero]
  have hv' : v = ∑ c, (N ^ s' c) (y' c) := by
    rw [hv, Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
  have hsum : ∑ c, s' c < ∑ c, s c := by
    rw [hs', Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase Finset.univ s (Finset.mem_univ a)]
    omega
  exact ⟨y', s', hy0', ⟨B', hB', hB'y⟩, hsle, hv', hsum⟩

theorem exists_good [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ (∀ a b, s a ≤ s b + (l a - l b)) ∧
      v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0 := by
  classical
  obtain ⟨ι, _, e, u, he, hu0, hli, hsp⟩ := GlobalTheory.CompanionTheory.JordanChain.exists_chain_basis N hN
  let B0 : Module.Basis (Σ a, Fin (e a)) E W := Basis.mk hli (by rw [hsp])
  have hB0p : ∀ p, B0 p = cbFam N e u p := fun p => by simp [B0, cbFam]
  have hB0 : IsChain N e B0 := cb_isChain_of_fam N e u hu0 B0 hB0p
  obtain ⟨y, s, hy0, hyg, hs, hv⟩ := cb_init N B0 hB0 he v
  obtain ⟨B1, hB1, hB1y⟩ := cb_exists_chain_of_gen N hN B0 hB0 he y hy0 hyg
  have hex : ∃ k, ∃ (y : ι → W) (s : ι → ℕ), ((∀ a, (N ^ e a) (y a) = 0) ∧
      (∃ B : Module.Basis (Σ a, Fin (e a)) E W, IsChain N e B ∧ ∀ p, B p = cbFam N e y p) ∧
      (∀ a, s a ≤ e a) ∧ v = ∑ a, (N ^ s a) (y a)) ∧ ∑ a, s a = k :=
    ⟨_, y, s, ⟨hy0, ⟨B1, hB1, hB1y⟩, hs, hv⟩, rfl⟩
  obtain ⟨y, s, ⟨hy0, ⟨B, hB, hBy⟩, hs, hv⟩, hk⟩ := Nat.find_spec hex
  have hC : ∀ a b, s a ≤ s b + (e a - e b) := by
    intro a b
    by_contra hab
    push Not at hab
    obtain ⟨y', s', h1, h2, h3, h4, h5⟩ := cb_step N hN he v y s hy0 B hB hBy hs hv a b hab
    exact Nat.find_min hex (hk ▸ h5) ⟨y', s', ⟨h1, h2, h3, h4⟩, rfl⟩
  refine ⟨ι, inferInstance, e, s, B, hB, he, hs, hC, ?_⟩
  rw [hv]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [hBy]; rfl
  · rw [show s a = e a by have := hs a; omega, hy0]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end
end
