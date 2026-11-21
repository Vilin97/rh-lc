module

public import Mathlib

@[expose] public section

open IsLocalRing

namespace GlobalTheory.DirectedNoeth

variable {S : Type} [CommRing S] [IsLocalRing S]

theorem mem_of_forall_mem_sup_pow (T : Subring S) [IsNoetherianRing T]
    (hmax : ((maximalIdeal S).comap T.subtype).map T.subtype = maximalIdeal S)
    (hpure : ∀ J : Ideal T, (J.map T.subtype).comap T.subtype = J)
    (A : Ideal T) (x : T) (hx : ∀ n : ℕ, (x : S) ∈ A.map T.subtype ⊔ maximalIdeal S ^ n) :
    x ∈ A := by
  set m : Ideal T := (maximalIdeal S).comap T.subtype with hm
  have hjac : m ≤ Ring.jacobson T := by
    intro y hy
    rw [Ring.mem_jacobson_iff]
    intro z
    have hu : T.subtype (y * z + 1) ∉ maximalIdeal S := by
      intro h
      have h1 : T.subtype (y * z) ∈ maximalIdeal S := by
        rw [map_mul]; exact Ideal.mul_mem_right _ _ hy
      have h2 := Ideal.sub_mem _ h h1
      rw [map_add (f := _), add_sub_cancel_left, map_one] at h2
      exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    have hunit : IsUnit (T.subtype (y * z + 1)) := by
      by_contra h
      exact hu ((mem_maximalIdeal _).mpr h)
    have h2 : Ideal.span {y * z + 1} = (⊤ : Ideal T) := by
      rw [← hpure (Ideal.span {y * z + 1}), Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_top.mpr hunit, Ideal.comap_top]
    exact Ideal.span_singleton_eq_top.mp h2
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := T ⧸ A) m hjac
  have hxn : ∀ n : ℕ, x ∈ A ⊔ m ^ n := by
    intro n
    have h := hx n
    rw [← hmax, ← Ideal.map_pow, ← Ideal.map_sup] at h
    rw [← hpure (A ⊔ m ^ n)]
    exact h
  have h0 : Ideal.Quotient.mk A x ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule T (T ⧸ A)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hxn n)
    have : Ideal.Quotient.mk A x = b • (1 : T ⧸ A) := by
      rw [← hab, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, Algebra.smul_def,
        mul_one, Ideal.Quotient.algebraMap_eq]
    rw [this]
    exact Submodule.smul_mem_smul hb trivial
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact h0

theorem mem_sup_pow_of_algebraMap_mem (K : Ideal S) (x : S)
    (hx : algebraMap S (AdicCompletion (maximalIdeal S) S) x ∈
      K.map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (n : ℕ) :
    x ∈ K ⊔ maximalIdeal S ^ n := by
  have h := Ideal.mem_map_of_mem (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom hx
  rw [Ideal.map_map] at h
  have hc : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom.comp
      (algebraMap S (AdicCompletion (maximalIdeal S) S)) = Ideal.Quotient.mk _ := by
    ext y
    simp [Ideal.Quotient.algebraMap_eq]
  rw [hc] at h
  have h' : Ideal.Quotient.mk (maximalIdeal S ^ n) x ∈ K.map (Ideal.Quotient.mk _) := by
    have e : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom
        (algebraMap S (AdicCompletion (maximalIdeal S) S) x) = Ideal.Quotient.mk _ x := by
      rw [← RingHom.comp_apply, hc]
    rw [← e]; exact h
  rw [Ideal.mem_quotient_iff_mem_sup] at h'
  exact h'

section

open Polynomial

private lemma coeff_mul_monomial_eq_ite {R : Type} [CommRing R] (p : R[X]) (d n : ℕ) (r : R) :
    (p * monomial d r).coeff n = if d ≤ n then p.coeff (n - d) * r else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

private theorem exists_leading_generators {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] (J : Ideal R) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → R) (d : ι → ℕ), (∀ i, f i ∈ J) ∧
      ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1) := by
  classical
  let shiftIdeal := I.map (algebraMap R (reesAlgebra I))
  have : IsNoetherianRing (reesAlgebra I ⧸ shiftIdeal) :=
    isNoetherianRing_reesAlgebra_quotient hI
  let lf : {p : ℕ × R // p.2 ∈ J ∧ p.2 ∈ I ^ p.1} → reesAlgebra I ⧸ shiftIdeal := fun x =>
    Ideal.Quotient.mk shiftIdeal ⟨monomial x.1.1 x.1.2, reesAlgebra.monomial_mem.mpr x.2.2⟩
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range lf)).mp
    (IsNoetherian.noetherian (Submodule.span (reesAlgebra I ⧸ shiftIdeal) (Set.range lf)))
  have hpre : ∀ q : s, ∃ x, lf x = q := fun q => hsS q.2
  choose pre hpre using hpre
  refine ⟨s, inferInstance, fun q => (pre q).1.2, fun q => (pre q).1.1, fun q => (pre q).2.1, ?_⟩
  intro n g hgJ hgn
  have hs : (↑s : Set (reesAlgebra I ⧸ shiftIdeal)) = Set.range fun q : s => (q : reesAlgebra I ⧸ shiftIdeal) := by
    ext x; simp
  have hmem : lf ⟨(n, g), hgJ, hgn⟩ ∈ Submodule.span (reesAlgebra I ⧸ shiftIdeal)
      (Set.range fun q : s => (q : reesAlgebra I ⧸ shiftIdeal)) := by
    rw [← hs, ← hspan]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  choose p hp using fun q => Ideal.Quotient.mk_surjective (I := shiftIdeal) (c q)
  have hz : (⟨monomial n g, reesAlgebra.monomial_mem.mpr hgn⟩ : reesAlgebra I) -
      ∑ q : s, p q * ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩
      ∈ shiftIdeal := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have hq : ∀ q : s, Ideal.Quotient.mk shiftIdeal (p q *
        ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩) =
        c q • (q : reesAlgebra I ⧸ shiftIdeal) := by
      intro q
      rw [map_mul, hp q, smul_eq_mul]
      exact congrArg _ (hpre q)
    simp only [hq, hc]
    exact sub_self _
  have hz := (mem_map_algebraMap_reesAlgebra_iff (I := I) _).mp hz
  refine ⟨fun q => if (pre q).1.1 ≤ n then ((p q : reesAlgebra I) : R[X]).coeff (n - (pre q).1.1)
    else 0, ?_, ?_⟩
  · intro q
    dsimp only
    split_ifs
    · exact (mem_reesAlgebra_iff I _).mp (p q).2 _
    · exact zero_mem _
  · convert hz n using 1
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      coeff_sub, finsetSum_coeff, coeff_mul_monomial_eq_ite, ite_mul, zero_mul]
    rw [coeff_monomial_same]

private theorem mem_span_of_leading {R : Type} [CommRing R] (I : Ideal R) [hc : IsAdicComplete I R]
    (J : Ideal R) {ι : Type} [Fintype ι] (f : ι → R) (d : ι → ℕ) (hf : ∀ i, f i ∈ J)
    (h : ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1))
    (g : R) (hg : g ∈ J) : g ∈ Ideal.span (Set.range f) := by
  classical
  have step : ∀ (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}), ∃ c : ι → R,
      (∀ i, c i ∈ I ^ (n - d i)) ∧ r.1 - ∑ i, c i * f i ∈ I ^ (n + 1) :=
    fun n r => h n r.1 r.2.1 r.2.2
  choose c hc1 hc2 using step
  let res : (n : ℕ) → {r : R // r ∈ J ∧ r ∈ I ^ n} := fun n =>
    Nat.rec (motive := fun n => {r : R // r ∈ J ∧ r ∈ I ^ n})
      ⟨g, hg, by simp⟩
      (fun n r => ⟨r.1 - ∑ i, c n r i * f i,
        J.sub_mem r.2.1 (J.sum_mem fun i _ => J.mul_mem_left _ (hf i)), hc2 n r⟩) n
  let a : ℕ → ι → R := fun n i => c n (res n) i
  have ha : ∀ n i, a n i ∈ I ^ (n - d i) := fun n i => hc1 n (res n) i
  have hres_succ : ∀ n, (res (n + 1)).1 = (res n).1 - ∑ i, a n i * f i := fun n => rfl
  have hdecomp : ∀ N, g = ∑ i, (∑ m ∈ Finset.range N, a m i) * f i + (res N).1 := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul, Finset.sum_const_zero, zero_add]
      rfl
    | succ N ih =>
      rw [hres_succ]
      simp only [Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
      conv_lhs => rw [ih]
      ring
  have hpow : ∀ {m n : ℕ} {x : R}, m ≤ n → x ∈ I ^ n → x ∈ I ^ m :=
    fun hmn hx => Ideal.pow_le_pow_right hmn hx
  have htop : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R R) = I ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let T : ι → ℕ → R := fun i k => ∑ m ∈ Finset.range (k + d i), a m i
  have hT : ∀ i {m n : ℕ}, m ≤ n → T i m ≡ T i n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro i m n hmn
    rw [SModEq.sub_mem, htop]
    have hd : T i n - T i m = ∑ k ∈ Finset.Ico (m + d i) (n + d i), a k i := by
      simp only [T]
      rw [Finset.sum_Ico_eq_sub _ (by omega)]
    rw [← neg_sub, hd]
    refine neg_mem (Ideal.sum_mem _ fun k hk => hpow ?_ (ha k i))
    rw [Finset.mem_Ico] at hk
    omega
  choose L hL using fun i => IsPrecomplete.prec' (I := I) (T i) (hT i)
  have hzero : g - ∑ i, L i * f i = 0 := by
    refine IsHausdorff.haus' (I := I) _ fun N => ?_
    rw [SModEq.sub_mem, sub_zero, htop]
    have hdD : ∀ i, d i ≤ ∑ j, d j := fun i =>
      Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    rw [hdecomp (N + ∑ j, d j)]
    have hS : ∀ i, ∑ m ∈ Finset.range (N + ∑ j, d j), a m i = T i (N + ∑ j, d j - d i) := by
      intro i
      simp only [T]
      rw [Nat.sub_add_cancel (by have := hdD i; omega)]
    have hrw : ∑ i, (∑ m ∈ Finset.range (N + ∑ j, d j), a m i) * f i + (res (N + ∑ j, d j)).1 -
        ∑ i, L i * f i =
        ∑ i, (T i (N + ∑ j, d j - d i) - L i) * f i + (res (N + ∑ j, d j)).1 := by
      simp only [hS, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hrw]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
      (hpow (by omega) (res (N + ∑ j, d j)).2.2)
    have hLi := hL i (N + ∑ j, d j - d i)
    rw [SModEq.sub_mem, htop] at hLi
    exact hpow (by have := hdD i; omega) hLi
  rw [sub_eq_zero] at hzero
  rw [hzero]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

private theorem isNoetherianRing_of_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R), I.FG →
    IsAdicComplete I R → IsNoetherianRing (R ⧸ I) → IsNoetherianRing R := by
  intro R _ I hI hc hq
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun J => ?_
  obtain ⟨ι, _, f, d, hf, hlead⟩ := exists_leading_generators I hI J
  have hJ : J = Ideal.span (Set.range f) := le_antisymm
    (fun g hg => mem_span_of_leading I J f d hf hlead g hg)
    (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf i))
  rw [hJ]
  exact Submodule.fg_span (Set.finite_range f)

end

theorem isNoetherianRing_completion (hfg : (maximalIdeal S).FG) :
    IsNoetherianRing (AdicCompletion (maximalIdeal S) S) := by
  refine isNoetherianRing_of_isAdicComplete _
    ((maximalIdeal S).map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (hfg.map _)
    (AdicCompletion.isAdicComplete_self _ hfg) ?_
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hfg]
  let := Ideal.Quotient.field (maximalIdeal S)
  have : IsNoetherianRing (S ⧸ maximalIdeal S) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (maximalIdeal S)).toRingHom)
      (AdicCompletion.evalOneₐ_surjective _)).symm

end GlobalTheory.DirectedNoeth

namespace GlobalTheory

open DirectedNoeth

theorem isNoetherianRing_of_directed_pure_union : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type)
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R →
    (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) →
    (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) →
    (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S := by
  intro S _ _ ι _ _ _ R hmono hcov hnoeth hmax hpure
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hfg : (maximalIdeal S).FG := by
    have := hnoeth i₁
    rw [← hmax i₁]
    exact (Ideal.fg_of_isNoetherianRing _).map _
  have := isNoetherianRing_completion hfg
  set f := algebraMap S (AdicCompletion (maximalIdeal S) S) with hf
  refine ⟨fun (I : Ideal S) => ?_⟩
  let E : ι → Ideal S := fun i => (I.comap (R i).subtype).map (R i).subtype
  have hEI : ∀ i, E i ≤ I := fun i => Ideal.map_comap_le
  have hEmono : Monotone E := by
    intro i j hij
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    have hyj : (y : S) ∈ R j := hmono hij y.2
    have : (⟨y, hyj⟩ : R j) ∈ I.comap (R j).subtype := hy
    exact Ideal.mem_map_of_mem (R j).subtype this
  obtain ⟨_, ⟨i₀, rfl⟩, hmaxl⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian (AdicCompletion (maximalIdeal S) S) (AdicCompletion (maximalIdeal S) S))
    (Set.range fun i => (E i).map f) (Set.range_nonempty _)
  have hfg0 : (E i₀).FG := by
    have := hnoeth i₀
    exact (Ideal.fg_of_isNoetherianRing _).map _
  suffices hle : I ≤ E i₀ by rw [le_antisymm hle (hEI i₀)]; exact hfg0
  intro x hx
  obtain ⟨k, hk⟩ := hcov x
  obtain ⟨j, hkj, hij⟩ := directed_of (· ≤ ·) k i₀
  have hxj : x ∈ R j := hmono hkj hk
  have hEj : (E j).map f = (E i₀).map f := by
    by_contra hne
    exact hmaxl _ ⟨j, rfl⟩ (lt_of_le_of_ne (Ideal.map_mono (hEmono hij)) (Ne.symm hne))
  have hfx : f x ∈ (E i₀).map f := by
    rw [← hEj]
    apply Ideal.mem_map_of_mem
    exact Ideal.mem_map_of_mem (R j).subtype (show (⟨x, hxj⟩ : R j) ∈ I.comap (R j).subtype from hx)
  have hij' : R i₀ ≤ R j := hmono hij
  let A : Ideal (R j) := (I.comap (R i₀).subtype).map (Subring.inclusion hij')
  have hA : A.map (R j).subtype = E i₀ := by
    simp only [A, E, Ideal.map_map]
    rfl
  have hxA : (⟨x, hxj⟩ : R j) ∈ A := by
    have := hnoeth j
    apply mem_of_forall_mem_sup_pow (R j) (hmax j) (hpure j) A
    intro n
    rw [hA]
    exact mem_sup_pow_of_algebraMap_mem (E i₀) x hfx n
  have := Ideal.mem_map_of_mem (R j).subtype hxA
  rwa [hA] at this

end GlobalTheory
