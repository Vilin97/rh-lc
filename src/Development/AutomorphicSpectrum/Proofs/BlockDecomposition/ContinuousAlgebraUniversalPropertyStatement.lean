module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulSubEqZeroOfSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementPropertiesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantToZModPow
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevelStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsUniqueForEpsilonRootStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSumStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousEpsilonPower

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv.EtaFn

section Var

variable {S : Type} [CommRing S] {l : ℕ} [Fact l.Prime] {ϖ x : S}

theorem pow_sub_one_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) (m : ℕ) :
    x ^ l ^ m - 1 ∈ Ideal.span {ϖ ^ l ^ m} := by
  rcases subsingleton_or_nontrivial S with h | h
  · rw [Subsingleton.elim (x ^ l ^ m - 1) 0]
    exact zero_mem _
  · haveI : CharP S l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl
    haveI : ExpChar S l := ExpChar.prime Fact.out
    have e : x ^ l ^ m - 1 = (x - 1) ^ l ^ m := by
      rw [sub_pow_char_pow, one_pow]
    rw [e, ← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hx _

theorem pow_sub_pow_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) {a b m : ℕ}
    (h : a ≡ b [MOD l ^ m]) : x ^ a - x ^ b ∈ Ideal.span {ϖ ^ l ^ m} := by
  have key : ∀ a b : ℕ, a ≤ b → a ≡ b [MOD l ^ m] → x ^ b - x ^ a ∈ Ideal.span {ϖ ^ l ^ m} := by
    intro a b hab h
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hab).1 h
    have hb : b = a + l ^ m * c := by omega
    obtain ⟨d, hd⟩ : x ^ l ^ m - 1 ∣ (x ^ l ^ m) ^ c - 1 := by
      simpa using sub_dvd_pow_sub_pow (x ^ l ^ m) 1 c
    have e : x ^ b - x ^ a = (x ^ l ^ m - 1) * (d * x ^ a) := by
      rw [hb, pow_add, pow_mul]
      linear_combination x ^ a * hd
    rw [e]
    exact Ideal.mul_mem_right _ _ (pow_sub_one_mem hl hx m)
  rcases le_total a b with hab | hab
  · rw [← neg_sub]
    exact neg_mem (key a b hab h)
  · exact key b a hab h.symm

theorem span_pow_le {k n : ℕ} (h : k ≤ n) : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ k} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ h)

theorem le_pow (k : ℕ) : k ≤ l ^ k := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem exists_lim [IsAdicComplete (Ideal.span {ϖ}) S] (hl : (l : S) = 0)
    (hx : x - 1 ∈ Ideal.span {ϖ}) (a : ℕ → ℕ) (ha : ∀ m m', m ≤ m' → a m' ≡ a m [MOD l ^ m]) :
    ∃ L, ∀ m, L - x ^ a m ∈ Ideal.span {ϖ ^ l ^ m} := by
  obtain ⟨L, hL⟩ := exists_tends (ϖ := ϖ) (fun m => x ^ a m) fun k =>
    ⟨k, fun m hm => span_pow_le (le_pow (l := l) k) (pow_sub_pow_mem hl hx (ha k m hm))⟩
  refine ⟨L, fun m => ?_⟩
  obtain ⟨M, hM⟩ := hL (l ^ m)
  have h1 := hM (max M m) (le_max_left _ _)
  have h2 := pow_sub_pow_mem (ϖ := ϖ) hl hx (ha m (max M m) (le_max_right _ _))
  have := sub_mem h2 h1
  convert this using 1
  ring

theorem eq_of_forall_mem [IsHausdorff (Ideal.span {ϖ}) S] {a b : S}
    (h : ∀ m, a - b ∈ Ideal.span {ϖ ^ l ^ m}) : a = b :=
  Tends.unique (ϖ := ϖ) (x := fun _ => a) (tends_const a)
    fun k => ⟨0, fun _ _ => span_pow_le (le_pow (l := l) k) (h k)⟩

end Var

variable {l : ℕ} [Fact l.Prime]

theorem val_modEq {m m' : ℕ} (h : m ≤ m') (z : ℤ_[l]) :
    (PadicInt.toZModPow m' z).val ≡ (PadicInt.toZModPow m z).val [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val,
    PadicInt.cast_toZModPow _ _ h]

theorem val_add_one (m : ℕ) (z : ℤ_[l]) :
    (PadicInt.toZModPow m (z + 1)).val ≡ (PadicInt.toZModPow m z).val + 1 [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    map_add, map_one, Nat.cast_one]

theorem exists_fn (A : PAlg l) (x : A.A) (hx : x - 1 ∈ Ideal.span {A.pi}) :
    ∃ η : (A.cont ℤ_[l]).A,
      (∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) η - x ^ (PadicInt.toZModPow m z).val ∈
        Ideal.span {A.pi ^ (l ^ m)}) ∧
      ∀ z : ℤ_[l], Hom.f (A.evCont (z + 1)) η = x * Hom.f (A.evCont z) η := by
  haveI hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have hl : (l : A.A) = 0 := A.natCast_l
  choose L hL using fun z : ℤ_[l] => exists_lim (ϖ := A.pi) hl hx
    (fun m => (PadicInt.toZModPow m z).val) (fun m m' h => val_modEq h z)
  refine ⟨⟨L, fun k => ?_⟩, fun m z => hL z m, fun z => ?_⟩
  · have e : (Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L =
        (fun c : ZMod (l ^ k) => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (x ^ c.val)) ∘
          PadicInt.toZModPow k := funext fun z =>
      Ideal.Quotient.eq.2 (span_pow_le (le_pow (l := l) k) (hL z k))
    have h : IsLocallyConstant ((Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L) := by
      rw [e]
      exact (GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l k).comp _
    exact h
  · refine eq_of_forall_mem (ϖ := A.pi) (l := l) fun m => ?_
    have h1 := hL (z + 1) m
    have h2 := Ideal.mul_mem_left _ x (hL z m)
    have h3 := pow_sub_pow_mem (ϖ := A.pi) hl hx (val_add_one m z)
    have := add_mem h1 (sub_mem h3 h2)
    change L (z + 1) - x * L z ∈ _
    convert this using 1
    ring

theorem exists_eta (ε : Eps l) : ∃ η : ((base l).cont ℤ_[l]).A,
    (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
    Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  have hx : (base l).s (ε.e 0) - 1 ∈ Ideal.span {(base l).pi} :=
    ((RL.sharp_cong (base l)).2.1 _ 1).1 (by
      rw [ε.sharp_e (base l), map_one, sub_self]
      exact zero_mem _)
  obtain ⟨η, h1, h2⟩ := exists_fn (base l) _ hx
  refine ⟨η, h1, cont_ext fun z => ?_⟩
  have e : Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) = (base l).s (ε.e 0) :=
    RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  rw [map_mul, e]
  exact h2 z

end GlobalTheory.CompanionTheory.ContUniv.EtaFn
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalProperty

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

variable {l : ℕ} [Fact l.Prime]

theorem sum_mul_sum_idem {T I : Type} [CommRing T] [Fintype I] {e : I → T}
    (h : CompleteOrthogonalIdempotents e) (a b : I → T) :
    (∑ i, e i * a i) * (∑ i, e i * b i) = ∑ i, e i * (a i * b i) := by
  classical
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have : e i * a i * (e i * b i) = (e i * e i) * (a i * b i) := by ring
    rw [this, h.idem i]
  · intro j _ hj
    have : e i * a i * (e j * b j) = (e i * e j) * (a i * b j) := by ring
    rw [this, h.ortho hj.symm, zero_mul]
  · simp

def rep {m : ℕ} (c : ZMod (l ^ m)) : ℤ_[l] := ((c.val : ℕ) : ℤ_[l])

theorem toZModPow_rep {m : ℕ} (c : ZMod (l ^ m)) : PadicInt.toZModPow m (rep c) = c := by
  rw [rep, map_natCast, ZMod.natCast_zmod_val]

theorem toZModPow_rep_of_le {m n : ℕ} (h : m ≤ n) (c : ZMod (l ^ n)) :
    PadicInt.toZModPow m (rep c) = ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c := by
  rw [rep, map_natCast, ZMod.natCast_val, ZMod.castHom_apply]

def stage {A : PAlg l} {T : Type} [CommRing T] (φ : A.A →+* T) {m : ℕ} (e : ZMod (l ^ m) → T)
    (he : CompleteOrthogonalIdempotents e) : (A.cont ℤ_[l]).A →+* T where
  toFun f := ∑ c, e c * φ (Hom.f (A.evCont (rep c)) f)
  map_one' := by simp only [map_one, mul_one]; exact he.complete
  map_mul' f g := by
    rw [sum_mul_sum_idem he]
    simp only [map_mul]
  map_zero' := by simp only [map_zero, mul_zero, Finset.sum_const_zero]
  map_add' f g := by
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem stage_apply {A : PAlg l} {T : Type} [CommRing T] (φ : A.A →+* T) {m : ℕ} (e : ZMod (l ^ m) → T)
    (he : CompleteOrthogonalIdempotents e) (f : (A.cont ℤ_[l]).A) :
    stage φ e he f = ∑ c, e c * φ (Hom.f (A.evCont (rep c)) f) := rfl

theorem hom_pi {A t : PAlg l} (φ : A ⟶ t) : Hom.f φ A.pi = t.pi :=
  RingHom.congr_fun (Hom.comm φ) (pFlat l)

theorem map_mem_span {A t : PAlg l} (φ : A ⟶ t) {k : ℕ} {x : A.A} (h : x ∈ Ideal.span {A.pi ^ k}) :
    Hom.f φ x ∈ Ideal.span {t.pi ^ k} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [map_mul, map_pow, hom_pi]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem stage_cauchy {A t : PAlg l} (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A)
    (he : ∀ m, CompleteOrthogonalIdempotents (e m))
    (hc : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c')
    (f : (A.cont ℤ_[l]).A) (k : ℕ) :
    ∃ M, ∀ m, M ≤ m → stage (Hom.f φ) (e m) (he m) f - stage (Hom.f φ) (e M) (he M) f ∈
      Ideal.span {t.pi ^ k} := by
  obtain ⟨M, hM⟩ := exists_period A f k
  refine ⟨M, fun m hm => ?_⟩
  have h1 : stage (Hom.f φ) (e M) (he M) f = ∑ c : ZMod (l ^ m), e m c * Hom.f φ (Hom.f (A.evCont
      (rep (ZMod.castHom (pow_dvd_pow l hm) (ZMod (l ^ M)) c))) f) := by
    rw [stage_apply, ← Finset.sum_fiberwise Finset.univ (ZMod.castHom (pow_dvd_pow l hm) (ZMod (l ^ M)))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hc M m hm d, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c hc' => ?_
    rw [(Finset.mem_filter.1 hc').2]
  rw [h1, stage_apply, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun c _ => ?_
  rw [← mul_sub, ← map_sub]
  refine Ideal.mul_mem_left _ _ (map_mem_span φ (hM _ _ ?_))
  rw [toZModPow_rep_of_le hm, toZModPow_rep]

theorem stage_ind {A t : PAlg l} (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A)
    (he : ∀ m, CompleteOrthogonalIdempotents (e m))
    (hc : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c')
    {m n : ℕ} (h : m ≤ n) (c : ZMod (l ^ m)) :
    stage (Hom.f φ) (e n) (he n) (ind A m c) = e m c := by
  rw [stage_apply, hc m n h c, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [ev_ind, toZModPow_rep_of_le h]
  split_ifs <;> simp

theorem map_exists (A t : PAlg l) (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A)
    (he : ∀ m, CompleteOrthogonalIdempotents (e m))
    (hc : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c') :
    ∃ ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ ∀ m c, Hom.f ψ (ind A m c) = e m c := by
  haveI : IsAdicComplete (Ideal.span {t.pi}) t.A := t.compl
  obtain ⟨ψ, hψ⟩ := exists_lim_hom (ϖ := t.pi) (fun m => stage (Hom.f φ) (e m) (he m))
    (stage_cauchy φ e he hc)
  have hconst : ∀ x : A.A, ψ (Hom.f (A.toCont ℤ_[l]) x) = Hom.f φ x := fun x => by
    refine (hψ _).unique ?_
    have : (fun m => stage (Hom.f φ) (e m) (he m) (Hom.f (A.toCont ℤ_[l]) x)) = fun _ => Hom.f φ x := by
      funext m
      rw [stage_apply]
      simp only [ev_toCont]
      rw [← Finset.sum_mul, (he m).complete, one_mul]
    rw [this]
    exact tends_const _
  have hcomm : ψ.comp (A.cont ℤ_[l]).s = t.s := RingHom.ext fun y => by
    have h := hconst (A.s y)
    exact h.trans (RingHom.congr_fun (Hom.comm φ) y)
  refine ⟨⟨ψ, hcomm⟩, Hom.ext (RingHom.ext hconst), fun m c => ?_⟩
  refine (hψ _).unique fun k => ⟨m, fun n hn => ?_⟩
  beta_reduce
  rw [stage_ind φ e he hc hn c, sub_self]
  exact zero_mem _

theorem map_unique {A t : PAlg l} (ψ ψ' : A.cont ℤ_[l] ⟶ t)
    (h1 : A.toCont ℤ_[l] ≫ ψ = A.toCont ℤ_[l] ≫ ψ')
    (h2 : ∀ m c, Hom.f ψ (ind A m c) = Hom.f ψ' (ind A m c)) : ψ = ψ' := by
  haveI : IsAdicComplete (Ideal.span {t.pi}) t.A := t.compl
  have hconst : ∀ x, Hom.f ψ (Hom.f (A.toCont ℤ_[l]) x) = Hom.f ψ' (Hom.f (A.toCont ℤ_[l]) x) :=
    fun x => congrArg (fun g : A ⟶ t => Hom.f g x) h1
  refine Hom.ext (RingHom.ext fun f => ?_)
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {t.pi}) t.A) _ fun k => ?_
  refine smodEq_iff.2 ?_
  rw [sub_zero]
  obtain ⟨M, hM⟩ := exists_period A f k
  let g : (A.cont ℤ_[l]).A := ∑ c, ind A M c * Hom.f (A.toCont ℤ_[l]) (Hom.f (A.evCont (rep c)) f)
  have hg : Hom.f ψ g = Hom.f ψ' g := by

    simp only [g, map_sum, map_mul, h2, hconst]
  have hfg : f - g ∈ Ideal.span {(A.cont ℤ_[l]).pi ^ k} := by
    refine (mem_span_pi_pow A k _).2 fun z => ?_
    have : Hom.f (A.evCont z) g = Hom.f (A.evCont (rep (PadicInt.toZModPow M z))) f := by

      simp only [g, map_sum, map_mul, ev_toCont, ev_ind]
      rw [Finset.sum_eq_single (PadicInt.toZModPow M z)]
      · simp
      · intro c _ hc
        rw [if_neg hc.symm, zero_mul]
      · simp
    rw [map_sub, this]
    exact hM _ _ (toZModPow_rep _).symm
  have h3 := map_mem_span ψ hfg
  have h4 := map_mem_span ψ' hfg
  have := sub_mem h3 h4
  rw [map_sub, map_sub, hg, sub_sub_sub_cancel_right] at this
  exact this

theorem map_existsUnique : ∀ {l : ℕ} [Fact l.Prime] (A t : PAlg l) (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A), (∀ m, CompleteOrthogonalIdempotents (e m)) →
  (∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)), e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c') →
  ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ ∀ m c, Hom.f ψ (ind A m c) = e m c := by
  intro l _ A t φ e he hc
  obtain ⟨ψ, h1, h2⟩ := map_exists A t φ e he hc
  exact ⟨ψ, ⟨h1, h2⟩, fun ψ' ⟨h3, h4⟩ => map_unique ψ' ψ (h3.trans h1.symm)
    fun m c => (h4 m c).trans (h2 m c).symm⟩

theorem level : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l), t.IsTest → ∀ (r : ℕ → t.A), (∀ m, r (m + 1) ^ l = r m) → t.sharp (r 0) = 1 →
  ∀ m, ∃ e : ZMod (l ^ m) → t.A, CompleteOrthogonalIdempotents e ∧ ∀ c, t.sharp (e c) * (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  intro l _ ε t ht r hr h1 m
  have hp := (GlobalTheory.T.epsilon_cyclotomic_element_properties ε).2.2.2.2 m
  have hz : t.sharp (r m) ^ l ^ m = 1 := by
    have : ∀ m, r m ^ l ^ m = r 0 := fun m => by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', pow_mul, hr, ih]
    rw [← map_pow, this, h1]
  obtain ⟨e, he, h⟩ := RL.mu_lc t ht.val_aic.1 m _ hp _ hz
  refine ⟨e, he, fun c => ?_⟩
  have h2 : t.oC (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) = t.sharp (t.s (ε.e m)) := by
    rw [oC_theta0, sW, WittVector.map_teichmuller]; rfl
  rw [← h2]
  exact h c

theorem formula (ε : Eps l) {ρ : ℕ → ((base l).cont ℤ_[l]).A}
    (hF : ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (ind (base l) m c) *
        ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val)
    {A t : PAlg l} (ψ : A.cont ℤ_[l] ⟶ t) (m : ℕ) :
    t.sharp (Hom.f ψ (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m))) =
      ∑ c : ZMod (l ^ m), t.sharp (Hom.f ψ (ind A m c)) * t.sharp (t.s (ε.e m)) ^ c.val := by
  have h := congrArg (mapU (contMap A.fromBase ℤ_[l] ≫ ψ)) (hF m)

  rw [mapU_sharp, map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
  rw [map_mul, map_pow, mapU_sharp, mapU_sharp]
  have h1 : Hom.f (contMap A.fromBase ℤ_[l] ≫ ψ) (ind (base l) m c) = Hom.f ψ (ind A m c) :=
    congrArg (Hom.f ψ) (contMap_ind A.fromBase m c)
  have h2 : Hom.f (contMap A.fromBase ℤ_[l] ≫ ψ) (((base l).cont ℤ_[l]).s (ε.e m)) = t.s (ε.e m) :=
    RingHom.congr_fun (Hom.comm (contMap A.fromBase ℤ_[l] ≫ ψ)) _
  rw [h1, h2]

theorem rel_of_formula {t : PAlg l} {m : ℕ} {E : ZMod (l ^ m) → t.A} (hE : CompleteOrthogonalIdempotents E)
    {x ξ : t.U} (hx : x = ∑ c, t.sharp (E c) * ξ ^ c.val) (c : ZMod (l ^ m)) :
    t.sharp (E c) * (x - ξ ^ c.val) = 0 :=
  mul_sub_eq_zero_of_sum (a := fun c => t.sharp (E c)) (b := fun c : ZMod (l ^ m) => ξ ^ c.val)
    (fun i => by rw [← map_mul, hE.idem i]) (fun i j h => by rw [← map_mul, hE.ortho h, sharp_zero]) hx c

theorem continuous_algebra_universal_existsUnique (ε : Eps l) {ρ : ℕ → ((base l).cont ℤ_[l]).A} (hρ : ∀ m, ρ (m + 1) ^ l = ρ m)
    (hF : ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (ind (base l) m c) *
        ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val)
    (A t : PAlg l) (ht : t.IsTest) (φ : A ⟶ t) (u : (t.A)ˣ) (hu : t.sharp u = 1) :
    ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
      Hom.f ψ (Hom.f (contMap A.fromBase ℤ_[l]) (ρ 0)) = u := by
  obtain ⟨r, hr0, hr⟩ := exists_roots t (u : t.A)
  have hr1 : t.sharp (r 0) = 1 := by rw [hr0, hu]
  choose e he hrel using level ε t ht r hr hr1
  have hcomp : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c' := fun m n h c => by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.idempotents_coarsen_to_lower_level ε t r hr h (e n) (he n) (hrel n)
    exact congrFun (GlobalTheory.T.idempotents_unique_for_epsilon_root ε t m (t.sharp (r m)) (e m) _ (he m) h1 (hrel m) h2) c
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψ⟩ := map_existsUnique A t φ e he hcomp
  have hv : ∀ (ψ' : A.cont ℤ_[l] ⟶ t) (m : ℕ), Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ (m + 1))) ^ l =
      Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m)) := fun ψ' m => by
    rw [← map_pow, ← map_pow, hρ]
  refine ⟨ψ, ⟨hψ1, ?_⟩, fun ψ' ⟨h1, h2⟩ => hψ ψ' ⟨h1, fun m c => ?_⟩⟩
  · have hE : ∀ m, (fun c => Hom.f ψ (ind A m c)) = e m := fun m => funext (hψ2 m)
    have key : (fun m => Hom.f ψ (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m))) = r := by
      refine RL.tilt_inj t _ _ (hv ψ) hr fun m => ?_
      rw [formula ε hF ψ m]
      have := eq_sum_of_mul_sub (a := fun c => t.sharp (e m c))
        (b := fun c : ZMod (l ^ m) => t.sharp (t.s (ε.e m)) ^ c.val) (sum_sharp_eq_one t (he m)) (hrel m)
      rw [this]
      exact Finset.sum_congr rfl fun c _ => by rw [hψ2 m c]
    exact (congrFun key 0).trans hr0
  · have key : (fun m => Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m))) = r :=
      roots_unique t (h2.trans hr0.symm) (hv ψ') hr
    refine congrFun (GlobalTheory.T.idempotents_unique_for_epsilon_root ε t m (t.sharp (r m)) _ (e m) (coi_map ψ' m) (he m) (fun c => ?_) (hrel m)) c
    have := rel_of_formula (coi_map ψ' m) (formula ε hF ψ' m) c
    rwa [show Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m)) = r m from congrFun key m] at this

theorem main : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l),
    ∃ η : (((base l).cont ℤ_[l]).A)ˣ, ((base l).cont ℤ_[l]).sharp η = 1 ∧
      PAlg.Hom.f (CrystallineSemistableComparison.B.contShift (base l)) η =
        ((base l).cont ℤ_[l]).s (ε.e 0) * (η : ((base l).cont ℤ_[l]).A) ∧
      ∀ (A t : PAlg l), t.IsTest → ∀ (φ : A ⟶ t) (u : (t.A)ˣ), t.sharp u = 1 →
        ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
          PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) η) = u := by
  intro l _ ε
  have hx : (base l).s (ε.e 0) - 1 ∈ Ideal.span {(base l).pi} :=
    ((RL.sharp_cong (base l)).2.1 _ 1).1 (by
      rw [ε.sharp_e (base l), map_one, sub_self]
      exact zero_mem _)
  obtain ⟨η, hη, hshift⟩ := EtaFn.exists_fn (base l) _ hx
  have hs : PAlg.Hom.f (CrystallineSemistableComparison.B.contShift (base l)) η =
      ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
    refine cont_ext fun z => ?_
    have hev : Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) =
        (base l).s (ε.e 0) :=
      RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
    rw [map_mul, hev]
    exact hshift z
  obtain ⟨ρ, h0, hρ⟩ := exists_roots ((base l).cont ℤ_[l]) η
  have hF := GlobalTheory.T.sharp_epsilon_root_idempotent_sum ε ρ (fun m z => h0 ▸ hη m z) hρ
  have h1 : ((base l).cont ℤ_[l]).sharp η = 1 := by
    have h := hF 0
    rw [h0] at h
    rw [h, ← sum_sharp_eq_one ((base l).cont ℤ_[l]) (coi_ind (base l) 0)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : c.val = 0 := by
      have : c.val < 1 := lt_of_lt_of_eq (ZMod.val_lt c) (pow_zero l)
      omega
    rw [this, pow_zero, mul_one]
  obtain ⟨w, rfl⟩ := RL.unit_lift ((base l).cont ℤ_[l]) η (by rw [h1]; exact isUnit_one)
  refine ⟨w, h1, hs, fun A t ht φ u hu => ?_⟩
  have := continuous_algebra_universal_existsUnique ε hρ hF A t ht φ u hu
  rwa [h0] at this

end GlobalTheory.CompanionTheory.ContUniv
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalPropertyStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.continuous_algebra_universal_property : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : (((base l).cont ℤ_[l]).A)ˣ, ((base l).cont ℤ_[l]).sharp η = 1 ∧ PAlg.Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η ∧ ∀ (A t : PAlg l), t.IsTest → ∀ (φ : A ⟶ t) (u : (t.A)ˣ), t.sharp u = 1 → ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) η) = u := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.main | exact GlobalTheory.CompanionTheory.ContUniv.main | (intros; apply GlobalTheory.CompanionTheory.ContUniv.main <;> assumption)
end
end
