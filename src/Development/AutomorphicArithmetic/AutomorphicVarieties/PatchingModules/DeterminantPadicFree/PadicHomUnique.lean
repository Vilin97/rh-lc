module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDvrPs

section

@[expose] public section

open IsLocalRing


theorem UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      (p : ℕ) [Fact p.Prime] [CharP A p] [Finite (ResidueField A)] (t : A), Irreducible t →
      ∃ e : PowerSeries (ResidueField A) ≃+* A, e PowerSeries.X = t ∧
        ∀ c, residue A (e (PowerSeries.C c)) = c := by
  intro A _ _ _ _ p _ _ _ t ht
  classical
  haveI : Fintype (ResidueField A) := Fintype.ofFinite _
  have hH : ∀ x y : A, (∀ n : ℕ, x - y ∈ maximalIdeal A ^ n) → x = y := by
    intro x y h
    rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)]
    intro n
    rw [SModEq.sub_mem]
    simpa [Ideal.smul_eq_mul] using h n
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have htm : t ∈ maximalIdeal A := by
    rw [hm]
    exact Ideal.subset_span rfl
  have hpk : CharP (ResidueField A) p := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
    rw [← map_natCast (residue A), CharP.cast_eq_zero, map_zero]
  have hder : ∀ (n : ℕ) (a : A), (n : A) = 0 →
      Polynomial.eval a (Polynomial.derivative (Polynomial.X ^ n - Polynomial.X : Polynomial A))
        = -1 := by
    intro n a hn
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, hn,
      zero_mul, zero_sub]
  obtain ⟨nf, -, hq⟩ := FiniteField.card (ResidueField A) p
  set q := Fintype.card (ResidueField A) with hqdef
  have hq2 : 1 < q := Fintype.one_lt_card
  have hq0 : (q : A) = 0 := by
    rw [hq]
    push_cast
    simp [CharP.cast_eq_zero]
  have hU : ∀ x y : A, x ^ q = x → y ^ q = y → residue A x = residue A y → x = y := by
    intro x y hx hy hxy
    have hz : (x - y) ^ q = x - y := by
      rw [hq, sub_pow_char_pow, ← hq, hx, hy]
    have hzm : x - y ∈ maximalIdeal A := Ideal.Quotient.eq.mp hxy
    rw [← sub_eq_zero]
    have h1 : (x - y) * (1 - (x - y) ^ (q - 1)) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq2.le, hz, sub_self]
    have hu : IsUnit (1 - (x - y) ^ (q - 1)) := by
      apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      exact (mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ hzm _ (by omega))
    exact (mul_eq_zero.mp h1).resolve_right hu.ne_zero
  have hE : ∀ c : ResidueField A, ∃ x : A, x ^ q = x ∧ residue A x = c := by
    intro c
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective c
    have hmon : (Polynomial.X ^ q - Polynomial.X : Polynomial A).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hq2
    have he1 : Polynomial.eval a₀ (Polynomial.X ^ q - Polynomial.X : Polynomial A)
        ∈ maximalIdeal A := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ha₀, FiniteField.pow_card,
        sub_self]
    have he2 : IsUnit (Ideal.Quotient.mk (maximalIdeal A) (Polynomial.eval a₀
        (Polynomial.derivative (Polynomial.X ^ q - Polynomial.X : Polynomial A)))) := by
      rw [hder q a₀ hq0, map_neg, map_one]
      exact isUnit_one.neg
    obtain ⟨a, ha, ham⟩ := HenselianRing.is_henselian (I := maximalIdeal A)
      (Polynomial.X ^ q - Polynomial.X : Polynomial A) hmon a₀ he1 he2
    refine ⟨a, ?_, ?_⟩
    · have h' := ha
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X] at h'
      exact sub_eq_zero.mp h'
    · rw [← ha₀]
      exact Ideal.Quotient.eq.mpr ham
  choose s0 hs0 using hE
  have hsq : ∀ c, s0 c ^ q = s0 c := fun c => (hs0 c).1
  have hsr : ∀ c, residue A (s0 c) = c := fun c => (hs0 c).2
  have hq0' : q ≠ 0 := by omega
  let s : ResidueField A →+* A :=
    { toFun := s0
      map_one' := hU _ _ (hsq 1) (one_pow _) (by rw [hsr, map_one])
      map_mul' := fun a b => hU _ _ (hsq _) (by rw [mul_pow, hsq, hsq])
        (by rw [hsr, map_mul, hsr, hsr])
      map_zero' := hU _ _ (hsq 0) (zero_pow hq0') (by rw [hsr, map_zero])
      map_add' := fun a b => hU _ _ (hsq _) (by rw [hq, add_pow_char_pow, ← hq, hsq, hsq])
        (by rw [hsr, map_add (f := _), hsr, hsr]) }
  have hsr' : ∀ c, residue A (s c) = c := hsr
  have hev : ∀ n (f : PowerSeries (ResidueField A)),
      (PowerSeries.trunc n f).eval₂ s t =
        ∑ i ∈ Finset.range n, s (PowerSeries.coeff i f) * t ^ i := fun n f =>
    PowerSeries.eval₂_trunc_eq_sum_range t s n f
  have key : ∀ n (P Q : Polynomial (ResidueField A)), (∀ i < n, P.coeff i = Q.coeff i) →
      Ideal.Quotient.mk (maximalIdeal A ^ n) (P.eval₂ s t) =
        Ideal.Quotient.mk (maximalIdeal A ^ n) (Q.eval₂ s t) := by
    intro n P Q h
    rw [Ideal.Quotient.eq, ← Polynomial.eval₂_sub]
    obtain ⟨R, hR⟩ := (Polynomial.X_pow_dvd_iff (f := P - Q) (n := n)).mpr
      (fun d hd => by rw [Polynomial.coeff_sub, h d hd, sub_self])
    rw [hR, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n)
  let g : (n : ℕ) → PowerSeries (ResidueField A) →+* A ⧸ maximalIdeal A ^ n := fun n =>
    { toFun := fun f => Ideal.Quotient.mk (maximalIdeal A ^ n) ((PowerSeries.trunc n f).eval₂ s t)
      map_one' := by
        rw [key n _ 1 (fun i hi => ?_), Polynomial.eval₂_one, map_one]
        simp [PowerSeries.coeff_trunc, hi, PowerSeries.coeff_one, Polynomial.coeff_one]
      map_mul' := fun f g' => by
        rw [← map_mul, ← Polynomial.eval₂_mul]
        apply key
        intro i hi
        rw [← PowerSeries.trunc_trunc_mul_trunc, PowerSeries.coeff_trunc, if_pos hi,
          ← Polynomial.coe_mul, Polynomial.coeff_coe]
      map_zero' := by simp [hev]
      map_add' := fun f g' => by simp [hev, add_mul, Finset.sum_add_distrib] }
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (g n) = g m := by
    intro m n hle
    ext f
    show Ideal.Quotient.factorPow (maximalIdeal A) hle
        (Ideal.Quotient.mk _ ((PowerSeries.trunc n f).eval₂ s t)) =
      Ideal.Quotient.mk _ ((PowerSeries.trunc m f).eval₂ s t)
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    apply key
    intro i hi
    simp [PowerSeries.coeff_trunc, hi, lt_of_lt_of_le hi hle]
  let e0 := IsAdicComplete.liftRingHom (maximalIdeal A) g hg
  have hme : ∀ n f, Ideal.Quotient.mk (maximalIdeal A ^ n) (e0 f) = g n f :=
    fun n f => IsAdicComplete.mk_liftRingHom (maximalIdeal A) g hg n f
  have hEq : ∀ n f, e0 f - (PowerSeries.trunc n f).eval₂ s t ∈ maximalIdeal A ^ n :=
    fun n f => Ideal.Quotient.eq.mp (hme n f)
  have hres : ∀ f, residue A (e0 f) = PowerSeries.constantCoeff f := by
    intro f
    have h1 := hEq 1 f
    rw [pow_one, hev, Finset.sum_range_one, pow_zero, mul_one] at h1
    have h2 : residue A (e0 f) = residue A (s (PowerSeries.coeff 0 f)) :=
      Ideal.Quotient.eq.mpr h1
    rw [h2, hsr', PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hmono : ∀ x : A, (∀ n, x ∈ maximalIdeal A ^ (n + 2)) → ∀ n, x ∈ maximalIdeal A ^ n :=
    fun x h n => Ideal.pow_le_pow_right (by omega) (h n)
  have hX : e0 PowerSeries.X = t := by
    apply hH
    apply hmono
    intro n
    have h1 := hEq (n + 2) PowerSeries.X
    have h2 : (PowerSeries.trunc (n + 2) PowerSeries.X).eval₂ s t = t := by
      rw [hev, Finset.sum_range_succ', Finset.sum_range_succ']
      simp [PowerSeries.coeff_X]
    rwa [h2] at h1
  have hinj : Function.Injective e0 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hdec := PowerSeries.X_pow_order_mul_divXPowOrder (f := f)
    have hu : residue A (e0 (PowerSeries.divXPowOrder f)) ≠ 0 := by
      rw [hres]
      exact (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff).not.mpr hne
    have hu' : e0 (PowerSeries.divXPowOrder f) ≠ 0 := fun h => hu (by rw [h, map_zero])
    rw [← hdec, map_mul, map_pow, hX] at hf
    exact mul_ne_zero (pow_ne_zero _ ht.ne_zero) hu' hf
  have hδ : ∀ x : A, ∃ y, y * t = x - s (residue A x) := by
    intro x
    rw [← Ideal.mem_span_singleton', ← hm, ← IsLocalRing.residue_eq_zero_iff, map_sub, hsr',
      sub_self]
  choose δ hδ using hδ
  have hsurj : Function.Surjective e0 := by
    intro x
    let F : PowerSeries (ResidueField A) := PowerSeries.mk fun n => residue A (δ^[n] x)
    have hc : ∀ n, x = (PowerSeries.trunc n F).eval₂ s t + t ^ n * δ^[n] x := by
      intro n
      induction n with
      | zero => simp [hev]
      | succ n ih =>
        rw [hev, Finset.sum_range_succ, ← hev, Function.iterate_succ_apply']
        have hcn : PowerSeries.coeff n F = residue A (δ^[n] x) := PowerSeries.coeff_mk _ _
        rw [hcn]
        linear_combination ih - t ^ n * hδ (δ^[n] x)
    refine ⟨F, hH _ _ fun n => ?_⟩
    have h1 := hEq n F
    have h2 : e0 F - x = (e0 F - (PowerSeries.trunc n F).eval₂ s t) - t ^ n * δ^[n] x := by
      linear_combination -(hc n)
    rw [h2]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n))
  refine ⟨RingEquiv.ofBijective e0 ⟨hinj, hsurj⟩, hX, fun c => ?_⟩
  show residue A (e0 (PowerSeries.C c)) = c
  rw [hres, PowerSeries.constantCoeff_C]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PadicHomUnique

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem padic_hom_unique {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (hl : (l : R) = 0)
    (f g : ℤ_[l] →+* R) : f = g := by
  ext z
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 z)
  have hz : z = y * (l : ℤ_[l]) + (z.appr 1 : ℤ_[l]) := by
    rw [pow_one] at hy; rw [hy]; ring
  rw [hz]
  simp [hl]

private theorem adic_push {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R')
    [IsLocalHom f] {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact map_nonunit f y hy
  exact (ha N).comp (Ideal.quotientMap _ f hle)

private theorem span_push {K K' : Type} [Field K] [Field K'] {n a : ℕ} (j : PowerSeries K →+* PowerSeries K')
    (hj : Function.Injective j) (S : Set (Matrix (Fin n) (Fin n) (PowerSeries K)))
    (h : ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) S) :
    ∀ Z ∈ Ev (PowerSeries K') (PowerSeries K') n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K') ^ s • Z ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
  have hmap : ∀ M ∈ Submodule.span (PowerSeries K) S,
      M.map j ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM => exact Submodule.subset_span ⟨M, hM, rfl⟩
    | zero => simp
    | add M N _ _ h1 h2 => rw [Matrix.map_add _ (map_add j)]; exact add_mem h1 h2
    | smul c M _ h1 =>
      have : (c • M).map j = j c • M.map j := by ext1 p q; simp
      rw [this]; exact Submodule.smul_mem _ _ h1
  have hX : j PowerSeries.X ≠ 0 := fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hX (PowerSeries.X_irreducible (R := K'))
  obtain ⟨u, hu⟩ := hm.dvd
  intro Z hZ
  have key : ∀ p q : Fin n, ∃ s : ℕ, (PowerSeries.X : PowerSeries K') ^ s • Matrix.single p q (Z p q) ∈
      Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro p q
    by_cases hpq : ((p : ℕ) < a) ↔ ((q : ℕ) < a)
    · have hE : Matrix.single p q (1 : PowerSeries K) ∈ Ev (PowerSeries K) (PowerSeries K) n a := by
        intro p' q'
        refine ⟨fun _ => trivial, fun e => ?_⟩
        rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact e hpq
      obtain ⟨s, hs⟩ := h _ hE
      refine ⟨m * s, ?_⟩
      have : (PowerSeries.X : PowerSeries K') ^ (m * s) • Matrix.single p q (Z p q) =
          (u ^ s * Z p q) • ((PowerSeries.X : PowerSeries K) ^ s • Matrix.single p q (1 : PowerSeries K)).map j := by
        ext1 p' q'
        rw [pow_mul, hu]
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs
        · simp only [mul_one, map_pow]; ring
        · simp
      rw [this]
      exact Submodule.smul_mem _ _ (hmap _ hs)
    · have : Z p q = 0 := (Submodule.mem_bot _).1 ((hZ p q).2 hpq)
      exact ⟨0, by simp [this]⟩
  choose s hs using key
  refine ⟨∑ p, ∑ q, s p q, ?_⟩
  rw [Matrix.matrix_eq_sum_single Z, Finset.smul_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  have hle : s p q ≤ ∑ p, ∑ q, s p q :=
    le_trans (Finset.single_le_sum (f := fun q => s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))
      (Finset.single_le_sum (f := fun p => ∑ q, s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hle
  rw [hd, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ (hs p q)

private theorem pushCh_inj {H A B : Type} [Group H] [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) {χ χ' : H →* Aˣ} (h : pushCh f χ = pushCh f χ') : χ = χ' := by
  ext g
  exact hf (congrArg Units.val (DFunLike.congr_fun h g))

private noncomputable def pushNP {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (K' : Type) [Field K'] [Finite K']
    [Algebra ℤ_[l] K'] (j : x.A →+* PowerSeries K') (hj : Function.Injective j) [IsLocalHom j]
    (he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries K')) : NP F n where
  K := K'
  ρ := pushRep j x.ρ
  cont p q := adic_push j (x.cont p q)
  form g := by
    have h := congrArg (fun M => M.map j) (x.form g)
    have h1 : mat (pushRep j x.ρ) g = (mat x.ρ g).map j := rfl
    have h2 : mat (pushRep j x.ρ) (F.conj g) = (mat x.ρ (F.conj g)).map j := rfl
    have h3 : ((F.eps ℤ_[l] (PowerSeries K') g ^ (1 - (n : ℤ)) : (PowerSeries K')ˣ) : PowerSeries K') =
        j ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) := by
      rw [← he]
      exact (congrArg Units.val (map_zpow (Units.map (j : x.A →* PowerSeries K')) _ _)).symm
    rw [h1, h2, h3]
    simp only [Units.val_one, mul_one, Matrix.map_mul] at h ⊢
    rw [← Matrix.transpose_map, h]
    ext1 p q
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  a := x.a
  a_pos := x.a_pos
  a_le := x.a_le
  blk g p q := ⟨fun _ => trivial, fun e => by
    have : mat x.ρ g p q = 0 := (x.blk g p q).2 e
    show j (mat x.ρ g p q) = 0
    rw [this, map_zero]⟩
  span Z hZ := by
    have := span_push j hj _ x.span Z hZ
    rwa [Set.image_image] at this
  ine u g hg := by
    show GeneralLinearGroup.map j (x.ρ g) = 1
    rw [x.ine u g hg, map_one]
  ψ v i := pushCh j (x.ψ v i)
  ψ_mu v i g hg := by
    show Units.map _ (x.ψ v i g) = 1
    rw [x.ψ_mu v i g hg, map_one]
  w v := GeneralLinearGroup.map j (x.w v)
  ty := x.ty
  w_blk v p q e := by
    show j (x.w v p q) = 0
    rw [x.w_blk v p q e, map_zero]
  tri v g := by
    have e : (GeneralLinearGroup.map j (x.w v))⁻¹ * pushRep j x.ρ (F.φ v g) * GeneralLinearGroup.map j (x.w v) =
        GeneralLinearGroup.map j ((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v) := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [e]
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p q) = 0
      rw [(x.tri v g).1 p q hpq, map_zero]
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p p) = j _
      rw [(x.tri v g).2 p]
  N1 v := by
    refine ⟨fun p q hpq e => (x.N1 v).1 p q hpq (pushCh_inj hj e), fun p q hpq e => (x.N1 v).2 p q hpq (pushCh_inj hj ?_)⟩
    rw [e, ← he]
    ext g
    simp

theorem UpperTheory.V.Pa.Det.extEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (A' : Type) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [IsEqDVR l A'] (j₀ : x.A →+* A'), Function.Injective j₀ → IsLocalHom j₀ → j₀.Finite → ∃ (x' : NP F n) (j : x.A →+* x'.A) (e : x'.A ≃+* A'), x.Ext2 x' j ∧ (∀ a, e (j a) = j₀ a) ∧ Nat.card x'.K = Nat.card (ResidueField A') := by
  intro l _ F n x A' _ _ _ hA j₀ hinj hloc hfin
  haveI := hA.complete
  haveI := hA.finite
  haveI := hA.char
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A'
  obtain ⟨e, -, -⟩ := UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr A' l t ht
  letI : Algebra ℤ_[l] (ResidueField A') := ((residue A').comp (j₀.comp (algebraMap ℤ_[l] x.A))).toAlgebra
  let j : x.A →+* PowerSeries (ResidueField A') := (e.symm : A' →+* _).comp j₀
  have hj : Function.Injective j := e.symm.injective.comp hinj
  haveI hl : IsLocalHom j := ⟨fun a ha => hloc.1 a (by simpa using ha.map e)⟩
  have hjf : j.Finite := RingHom.Finite.comp (RingHom.Finite.of_surjective _ e.symm.surjective) hfin
  have h0 : (l : PowerSeries (ResidueField A')) = 0 := e.injective (by simp)
  have he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries (ResidueField A')) := by
    have := padic_hom_unique h0 (j.comp ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])))
      ((algebraMap ℤ_[l] _).comp (algebraMap ℤ_[l] ℤ_[l]))
    unfold GFrame.eps
    rw [← this]
    rfl
  exact ⟨pushNP x (ResidueField A') j hj he, j, e, ⟨⟨hj, hl, hjf, rfl, rfl, fun _ _ => rfl⟩, fun _ => rfl, rfl⟩,
    fun a => e.apply_symm_apply _, rfl⟩
end
end
