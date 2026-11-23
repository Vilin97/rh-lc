module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
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
import Std.Tactic.BVDecide.Normalize.Bool
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.EquivLift
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SymbolFirstFamilyOfMem

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} (ε : Fin m → Bool)

def U (N : ℕ) : Set ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) :=
  {t | (t.sum fun _ e => e) ≤ N ∧ ∀ v ∈ t.support, inF1 ε (Sum.elim id id v)}

def S (N : ℕ) : Submodule ℂ (Sym m n) := restrictSupport ℂ (U ε N)

variable {ε}

theorem mem_S {N : ℕ} {s : Sym m n} : s ∈ S ε N ↔ ∀ t ∈ s.support, t ∈ U ε N := by
  unfold S
  rw [mem_restrictSupport_iff]
  exact ⟨fun h t ht => h ht, fun h t ht => h t ht⟩

theorem symbol_first_family_of_mem {N : ℕ} {s : Sym m n} (h : s ∈ S ε N) : SymbolInFirstFamily ε s := by
  intro t ht k hk
  have hU := (mem_S.1 h t ht).2
  rcases hk with hk | hk
  · exact hU (Sum.inl k) (Finsupp.mem_support_iff.2 hk)
  · exact hU (Sum.inr k) (Finsupp.mem_support_iff.2 hk)

theorem mem_S_of {s : Sym m n} (h : SymbolInFirstFamily ε s) : s ∈ S ε s.totalDegree := by
  refine mem_S.2 fun t ht => ⟨le_totalDegree ht, fun v hv => ?_⟩
  rcases v with k | k
  · exact h t ht k (Or.inl (Finsupp.mem_support_iff.1 hv))
  · exact h t ht k (Or.inr (Finsupp.mem_support_iff.1 hv))

theorem S_le (N : ℕ) : S (n := n) ε N ≤ restrictTotalDegree ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) ℂ N := by
  intro s hs
  rw [mem_restrictTotalDegree, totalDegree, Finset.sup_le_iff]
  exact fun t ht => (mem_S.1 hs t ht).1

instance (N : ℕ) : FiniteDimensional ℂ (S (n := n) ε N) :=
  Submodule.finiteDimensional_of_le (S_le N)

theorem symK_X (i j : Fin n) (v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) :
    symK ε i j (X v) = 0 ∨ ∃ v', ∃ c : ℂ, symK ε i j (X v) = c • (X v' : Sym m n) ∧ inF1 ε (Sum.elim id id v') := by
  unfold symK
  rw [mkDerivation_X]
  rcases v with ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · by_cases ha : ε a = true
    · rw [if_pos ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inl (a, i, false), 1, by simp, by simp [inF1, ha]⟩
      · exact Or.inl rfl
    · rw [if_neg ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inl (a, j, true), -1, by simp, by simp [inF1]; simpa using ha⟩
      · exact Or.inl rfl
  · by_cases ha : ε a = true
    · rw [if_pos ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inr (a, j, false), -1, by simp, by simp [inF1, ha]⟩
      · exact Or.inl rfl
    · rw [if_neg ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inr (a, i, true), 1, by simp, by simp [inF1]; simpa using ha⟩
      · exact Or.inl rfl

theorem monomial_mem_S {N : ℕ} {u} (hu : u ∈ U ε N) (r : ℂ) : monomial u r ∈ S (n := n) ε N := by
  refine mem_S.2 fun t ht => ?_
  have := support_monomial_subset ht
  rw [Finset.mem_singleton] at this
  exact this ▸ hu

theorem deg_add (a b : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) :
    ((a + b).sum fun _ e => e) = (a.sum fun _ e => e) + (b.sum fun _ e => e) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem symK_monomial_mem {N : ℕ} (i j : Fin n) {t} (ht : t ∈ U ε N) (r : ℂ) :
    symK ε i j (monomial t r) ∈ S (n := n) ε N := by
  unfold symK
  rw [mkDerivation_monomial]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun v hv => ?_)
  dsimp only
  have hsymk := symK_X (ε := ε) i j v
  unfold symK at hsymk
  rw [mkDerivation_X] at hsymk
  rcases hsymk with h0 | ⟨v', c, hc, hv'⟩
  · rw [h0, smul_zero]; exact Submodule.zero_mem _
  · rw [hc, smul_eq_mul, mul_smul_comm, X, monomial_mul]
    refine Submodule.smul_mem _ _ (monomial_mem_S ⟨?_, ?_⟩ _)
    · have hle : Finsupp.single v 1 ≤ t := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)
      have e1 := deg_add (t - Finsupp.single v 1) (Finsupp.single v 1)
      rw [tsub_add_cancel_of_le hle] at e1
      rw [deg_add]
      have : ((Finsupp.single v' 1 : _ →₀ ℕ).sum fun _ e => e) = ((Finsupp.single v 1 : _ →₀ ℕ).sum fun _ e => e) := by
        simp [Finsupp.sum_single_index]
      rw [this, ← e1]; exact ht.1
    · intro w hw
      rcases Finset.mem_union.1 (Finsupp.support_add hw) with hw | hw
      · exact ht.2 w (Finsupp.support_tsub hw)
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hw
        exact hw ▸ hv'

theorem symK_mem {N : ℕ} (i j : Fin n) {s : Sym m n} (hs : s ∈ S ε N) : symK ε i j s ∈ S ε N := by

  rw [as_sum s, map_sum]
  exact Submodule.sum_mem _ fun t ht => symK_monomial_mem i j (mem_S.1 hs t ht) _

end CoreD

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SymKEqZeroOfOm

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} {ε : Fin m → Bool}

def psi (p q : Sym m n) : ℂ :=
  ∑ u ∈ p.support ∪ q.support, star (p.coeff u) * q.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)

theorem psi_eq (p q : Sym m n) (T : Finset _) (h : p.support ∪ q.support ⊆ T) :
    psi p q = ∑ u ∈ T, star (p.coeff u) * q.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ) := by
  unfold psi
  refine Finset.sum_subset h fun u _ hu => ?_
  rw [Finset.mem_union, not_or, mem_support_iff, mem_support_iff, not_not, not_not] at hu
  simp [hu.1, hu.2]

theorem psi_add_right (p q₁ q₂ : Sym m n) : psi p (q₁ + q₂) = psi p q₁ + psi p q₂ := by
  classical
  have h0 : (q₁ + q₂).support ⊆ q₁.support ∪ q₂.support := support_add
  rw [psi_eq p (q₁ + q₂) (p.support ∪ q₁.support ∪ q₂.support) (by
      intro u hu; rcases Finset.mem_union.1 hu with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · rcases Finset.mem_union.1 (h0 h) with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ h'),
    psi_eq p q₁ (p.support ∪ q₁.support ∪ q₂.support) (Finset.union_subset_left le_rfl),
    psi_eq p q₂ (p.support ∪ q₁.support ∪ q₂.support)
      (Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem psi_herm (p q : Sym m n) : psi q p = star (psi p q) := by
  unfold psi
  rw [Finset.union_comm, star_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [star_mul', star_star, star_prod, star_natCast]
  ring

theorem psi_pos (p : Sym m n) (hp : p ≠ 0) : 0 < (psi p p).re := by
  unfold psi
  rw [Finset.union_self, Complex.re_sum]
  have hterm : ∀ u, (star (p.coeff u) * p.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)).re =
      Complex.normSq (p.coeff u) * ∏ k ∈ u.support, ((u k).factorial : ℝ) := by
    intro u
    have : star (p.coeff u) * p.coeff u = (Complex.normSq (p.coeff u) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this, show (∏ k ∈ u.support, ((u k).factorial : ℂ)) = ((∏ k ∈ u.support, ((u k).factorial : ℝ) : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hp)
  refine Finset.sum_pos' (fun v _ => mul_nonneg (Complex.normSq_nonneg _)
    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)) ⟨u, hu, mul_pos ?_ (Finset.prod_pos fun _ _ => by
      exact_mod_cast Nat.factorial_pos _)⟩
  exact Complex.normSq_pos.2 (mem_support_iff.1 hu)

theorem psi_sum_right {ι : Type*} (p : Sym m n) (F : Finset ι) (f : ι → Sym m n) :
    psi p (∑ x ∈ F, f x) = ∑ x ∈ F, psi p (f x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [psi]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, psi_add_right, ih]

theorem psi_sum_left {ι : Type*} (p : Sym m n) (F : Finset ι) (f : ι → Sym m n) :
    psi (∑ x ∈ F, f x) p = ∑ x ∈ F, psi (f x) p := by
  rw [psi_herm, psi_sum_right, star_sum]
  exact Finset.sum_congr rfl fun x _ => (psi_herm _ _).symm


variable (ε) in
def Om : Module.End ℂ (Sym m n) :=
  ∑ ij : Fin n × Fin n, (symK ε ij.1 ij.2).toLinearMap * (symK ε ij.2 ij.1).toLinearMap

theorem Om_apply (s : Sym m n) : Om ε s = ∑ ij : Fin n × Fin n, symK ε ij.1 ij.2 (symK ε ij.2 ij.1 s) := by
  simp [Om, LinearMap.sum_apply]

theorem Om_mem {N : ℕ} {s : Sym m n} (hs : s ∈ S ε N) : Om ε s ∈ S ε N := by
  rw [Om_apply]
  exact Submodule.sum_mem _ fun ij _ => symK_mem _ _ (symK_mem _ _ hs)


variable (ε) in
def OmS (N : ℕ) : Module.End ℂ (S (n := n) ε N) := (Om ε).restrict fun _ hs => Om_mem hs

section adj

variable (hadj : ∀ (i j : Fin n) (s t : Sym m n), psi (symK ε i j s) t = psi s (symK ε j i t))
include hadj

theorem psi_Om (a b : Sym m n) : psi (Om ε a) b = psi a (Om ε b) := by
  rw [Om_apply, Om_apply, psi_sum_left, psi_sum_right]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [hadj, ← hadj ij.2 ij.1]

theorem psi_Om_diag (a : Sym m n) : psi a (Om ε a) = ∑ ij : Fin n × Fin n, psi (symK ε ij.2 ij.1 a) (symK ε ij.2 ij.1 a) := by
  rw [Om_apply, psi_sum_right]
  exact Finset.sum_congr rfl fun ij _ => (hadj ij.2 ij.1 a _).symm

theorem symK_eq_zero_of_Om (a : Sym m n) (h : Om ε a = 0) (i j : Fin n) : symK ε i j a = 0 := by
  have h0 := psi_Om_diag hadj a
  rw [h, show psi a 0 = 0 by simp [psi]] at h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ ij ∈ (Finset.univ : Finset (Fin n × Fin n)),
      0 ≤ (psi (symK ε ij.2 ij.1 a) (symK ε ij.2 ij.1 a)).re := fun ij _ => by
    by_cases hz : symK ε ij.2 ij.1 a = 0
    · rw [hz]; simp [psi]
    · exact (psi_pos _ hz).le
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre.symm (j, i) (Finset.mem_univ _)
  by_contra hz
  exact (psi_pos _ hz).ne' this

theorem ker_inf_range {N : ℕ} (v : S (n := n) ε N) (h0 : OmS ε N v = 0) (h1 : ∃ u, OmS ε N u = v) : v = 0 := by
  obtain ⟨u, rfl⟩ := h1
  have h0' : Om ε (OmS ε N u).1 = 0 := congrArg Subtype.val h0
  have : psi (OmS ε N u).1 (OmS ε N u).1 = 0 := by
    change psi (Om ε u.1) (Om ε u.1) = 0
    rw [psi_Om hadj]
    change psi u.1 (Om ε (OmS ε N u).1) = 0
    rw [h0']; simp [psi]
  by_contra hne
  have hne' : (OmS ε N u).1 ≠ 0 := fun h => hne (Subtype.ext h)
  exact (psi_pos _ hne').ne' (by rw [this]; simp)

theorem pow_kill {N : ℕ} (k : ℕ) (v : S (n := n) ε N) (h : (OmS ε N ^ (k + 1)) v = 0) : OmS ε N v = 0 := by
  induction k generalizing v with
  | zero => simpa using h
  | succ k ih =>
    have h' : (OmS ε N ^ (k + 1)) (OmS ε N v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ]; exact h
    exact ker_inf_range hadj _ (ih _ h') ⟨v, rfl⟩

theorem exists_q (N : ℕ) : ∃ q : Polynomial ℂ, q.eval 0 = 1 ∧ ∀ v, OmS ε N (Polynomial.aeval (OmS (n := n) ε N) q v) = 0 := by
  set T := OmS (n := n) ε N
  have hp : T.charpoly ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  obtain ⟨g, hpg, hg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hp 0
  rw [map_zero, sub_zero] at hpg hg
  have hg0 : g.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]; exact fun h => hg (Polynomial.X_dvd_iff.2 h)
  refine ⟨Polynomial.C (g.eval 0)⁻¹ * g, by simp [hg0], fun v => ?_⟩
  have hz : (Polynomial.aeval T T.charpoly) v = 0 := by rw [LinearMap.aeval_self_charpoly]; rfl
  rw [hpg, map_mul, map_pow, Polynomial.aeval_X, Module.End.mul_apply] at hz
  rw [map_mul, Module.End.mul_apply, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  rcases Nat.eq_zero_or_pos (Polynomial.rootMultiplicity 0 T.charpoly) with hk | hk
  · rw [hk, pow_zero, Module.End.one_apply] at hz
    rw [hz, map_zero, smul_zero]
  · obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_lt hk
    rw [hk', zero_add] at hz
    rw [pow_kill hadj k _ hz, smul_zero]

end adj

end CoreD

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.BoxLeFirstFamily

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} {ε : Fin m → Bool}

theorem opMono_add (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (f g : PX m n) :
    opMono t (f + g) = opMono t f + opMono t g := by
  simp [opMono, map_add (f := _), mul_add]

theorem opMono_smul (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (r : ℂ) (f : PX m n) :
    opMono t (r • f) = r • opMono t f := by
  simp [opMono, map_smul, mul_smul_comm]

def opL (s : Sym m n) : Module.End ℂ (PX m n) where
  toFun := op s
  map_add' f g := by simp [op, opMono_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by simp [op, opMono_smul, Finset.smul_sum, smul_comm r]

theorem op_eq (s : Sym m n) (T : Finset _) (h : s.support ⊆ T) (f : PX m n) :
    op s f = ∑ t ∈ T, s.coeff t • opMono t f := by
  unfold op
  refine Finset.sum_subset h fun t _ ht => ?_
  rw [mem_support_iff, not_not] at ht
  rw [ht, zero_smul]

theorem op_add_sym (s₁ s₂ : Sym m n) (f : PX m n) : op (s₁ + s₂) f = op s₁ f + op s₂ f := by
  classical
  rw [op_eq (s₁ + s₂) (s₁.support ∪ s₂.support) support_add, op_eq s₁ (s₁.support ∪ s₂.support)
    Finset.subset_union_left, op_eq s₂ (s₁.support ∪ s₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [MvPolynomial.coeff_add, add_smul]

theorem op_smul_sym (s : Sym m n) (r : ℂ) (f : PX m n) : op (r • s) f = r • op s f := by
  classical
  rw [op_eq (r • s) s.support support_smul, op, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

theorem op_sum_sym {ι : Type*} (F : Finset ι) (g : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ F, g i) f = ∑ i ∈ F, op (g i) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [op]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_sym, ih]

theorem box_le_first_family (R : Set (Fin m → ℕ)) : box (n := n) ε R ≤ F1 ε := by
  refine Submodule.span_le.2 fun p ⟨s, hs, _, hp⟩ => ?_
  subst hp
  change monomial s 1 ∈ MvPolynomial.supported ℂ {k | inF1 ε k}
  rw [MvPolynomial.mem_supported, vars_monomial one_ne_zero]
  exact fun k hk => hs k hk

def Ad {V : Submodule ℂ (PX m n)} (K : Module.End ℂ (PX m n)) (KV : Module.End ℂ V) :
    Module.End ℂ (V →ₗ[ℂ] PX m n) where
  toFun h := K ∘ₗ h - h ∘ₗ KV
  map_add' h₁ h₂ := LinearMap.ext fun f => by simp; abel
  map_smul' r h := LinearMap.ext fun f => by simp [smul_sub]

section main

variable (R : Set (Fin m → ℕ)) (hV : ∀ (i j : Fin n), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R)

def KV (i j : Fin n) : Module.End ℂ (box (n := n) ε R) := (KopL ε i j).restrict (hV i j)

def OmH : Module.End ℂ (box (n := n) ε R →ₗ[ℂ] PX m n) :=
  ∑ ij : Fin n × Fin n, Ad (KopL ε ij.1 ij.2) (KV R hV ij.1 ij.2) * Ad (KopL ε ij.2 ij.1) (KV R hV ij.2 ij.1)

def rr (N : ℕ) : S (n := n) ε N →ₗ[ℂ] (box (n := n) ε R →ₗ[ℂ] PX m n) where
  toFun x := opL x.1 ∘ₗ (box ε R).subtype
  map_add' x y := LinearMap.ext fun f => op_add_sym x.1 y.1 f.1
  map_smul' r x := LinearMap.ext fun f => op_smul_sym x.1 r f.1

variable (hS : SymKComm)
include hS

theorem rr_Om (N : ℕ) (x : S (n := n) ε N) : rr R N (OmS ε N x) = OmH R hV (rr R N x) := by
  refine LinearMap.ext fun f => ?_
  have hf : f.1 ∈ F1 ε := box_le_first_family R f.2
  have hF1 : ∀ (i j : Fin n) (g : box (n := n) ε R), (KopL ε i j g.1) ∈ F1 ε := fun i j g => box_le_first_family R (hV i j g.1 g.2)
  simp only [rr, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Submodule.coe_subtype, OmH,
    LinearMap.sum_apply, Module.End.mul_apply, opL]
  change op (Om ε x.1) f.1 = _
  rw [Om_apply, op_sum_sym]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have hx : SymbolInFirstFamily ε x.1 := symbol_first_family_of_mem x.2
  have hx' : SymbolInFirstFamily ε (symK ε ij.2 ij.1 x.1) := symbol_first_family_of_mem (symK_mem _ _ x.2)
  rw [hS m n ε ij.1 ij.2 _ hx' f.1 hf, hS m n ε ij.2 ij.1 _ hx f.1 hf,
    hS m n ε ij.2 ij.1 _ hx _ (hF1 ij.1 ij.2 f)]
  rfl

theorem rr_aeval (N : ℕ) (q : Polynomial ℂ) (x : S (n := n) ε N) :
    rr R N (Polynomial.aeval (OmS ε N) q x) = Polynomial.aeval (OmH R hV) q (rr R N x) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, LinearMap.map_smul_of_tower,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    congr 1
    induction k generalizing x with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, rr_Om R hV hS, pow_succ, Module.End.mul_apply]

end main

theorem aeval_ker {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (v : V) (h : T v = 0)
    (q : Polynomial ℂ) : Polynomial.aeval T q v = q.eval 0 • v := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add q]
  rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply, Module.End.mul_apply, h,
    map_zero, zero_add, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Polynomial.coeff_zero_eq_eval_zero]

end CoreD


open CoreD in
theorem equivLift_of (hFFT : PositivityTheory.Rg.Sw.FFT) (_hSF : SemiFam) (hD : Dens) (hS : SymKComm) (hI : InvOp)
    (hF : FormFacts) : EquivLift := by
  intro m n ε c hc R t ht htk
  obtain ⟨-, -, -, hF4, hF5⟩ := hF m n ε c hc
  have hadj : ∀ (i j : Fin n) (s u : Sym m n), psi (symK ε i j s) u = psi s (symK ε j i u) := fun i j s u => by
    have := (hF5 i j s u).2
    simpa [psi] using this
  have hV : ∀ (i j : Fin n), ∀ f ∈ box ε (R : Set (Fin m → ℕ)), KopL ε i j f ∈ box ε (R : Set (Fin m → ℕ)) :=
    fun i j f hf => hF4 i j _ f hf
  obtain ⟨s, hs1, hs2⟩ := hD m n ε R t (fun f hf => box_le_first_family _ (ht f hf))
  set N := s.totalDegree
  let x : S (n := n) ε N := ⟨s, mem_S_of hs1⟩
  obtain ⟨q, hq0, hq⟩ := exists_q hadj N
  set y := Polynomial.aeval (OmS ε N) q x with hy
  have ht' : OmH (R : Set (Fin m → ℕ)) hV (t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype) = 0 := by
    rw [OmH, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun ij _ => ?_
    have h0 : Ad (KopL ε ij.2 ij.1) (KV (R : Set (Fin m → ℕ)) hV ij.2 ij.1) (t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype) = 0 := by
      refine LinearMap.ext fun f => ?_
      simp [Ad, KV, LinearMap.restrict_apply, htk ij.2 ij.1 f.1 f.2]
    rw [Module.End.mul_apply, h0, map_zero]
  have hrx : rr (R : Set (Fin m → ℕ)) N x = t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype := by
    refine LinearMap.ext fun f => ?_
    exact hs2 f.1 f.2
  have hry : rr (R : Set (Fin m → ℕ)) N y = t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype := by
    rw [hy, rr_aeval _ hV hS, hrx, aeval_ker _ _ ht', hq0, one_smul]
  have hy0 : Om ε y.1 = 0 := congrArg Subtype.val (hq x)
  have hsym : ∀ i j, symK ε i j y.1 = 0 := symK_eq_zero_of_Om hadj _ hy0
  obtain ⟨w, hw, hwf⟩ := hI hFFT m n ε c hc y.1 (symbol_first_family_of_mem y.2) hsym
  refine ⟨w, hw, fun f hf => ?_⟩
  have h1 : op y.1 f = t f := LinearMap.congr_fun hry ⟨f, hf⟩
  rw [← h1, hwf f (box_le_first_family _ hf)]

end PositivityTheory.Rg.Sw.LC
end
end
end
