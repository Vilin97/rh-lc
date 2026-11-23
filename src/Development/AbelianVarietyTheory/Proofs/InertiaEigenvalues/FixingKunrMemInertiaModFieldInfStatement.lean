module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeMinpolyRootNegPrimeUnramified

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaDeg
open Polynomial

theorem natDegree_minpoly_root_neg_l : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (π : Om l), 0 < N → π ^ N = -(l : Om l) → ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → (minpoly E π).natDegree = N := by
  intro l _ N π hN hπ E _ _ hE
  have hl0 : (0 : ℝ) < l := by linarith [Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)]
  set Q : E[X] := Polynomial.X ^ N + Polynomial.C ((l : ℕ) : E) with hQ
  have hQm : Q.Monic := by
    rw [hQ]; exact monic_X_pow_add_C _ hN.ne'
  have hQr : aeval π Q = 0 := by
    rw [hQ]; simp [hπ]
  have hint : IsIntegral E π := ⟨Q, hQm, by rwa [aeval_def] at hQr⟩
  have hdvd : minpoly E π ∣ Q := minpoly.dvd _ _ hQr
  have hQdeg : Q.natDegree = N := by rw [hQ]; exact natDegree_X_pow_add_C
  have hle : (minpoly E π).natDegree ≤ N := by
    rw [← hQdeg]; exact natDegree_le_of_dvd hdvd hQm.ne_zero
  have hpos : 0 < (minpoly E π).natDegree := minpoly.natDegree_pos hint
  have hmon := minpoly.monic hint
  set P := (minpoly E π).map (algebraMap E (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hπn : ‖π‖ ^ N = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hπ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  have hroots : ∀ a ∈ P.roots, ‖a‖ = ‖π‖ := by
    intro a ha
    have h1 : P ∣ Q.map (algebraMap E (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : (Q.map (algebraMap E (Om l))).IsRoot a := (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ N = -(l : Om l) := by
      rw [hQ] at h2
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ N = ‖π‖ ^ N := by
      rw [← norm_pow, h3, ← hπ, norm_pow]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hN.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖π‖ ^ (minpoly E π).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap E (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖π‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = algebraMap E (Om l) ((minpoly E π).eval 0) := by
    rw [hP, Polynomial.eval_map, ← map_zero (algebraMap E (Om l)), Polynomial.eval₂_at_apply]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne', eq_comm, neg_eq_zero] at hπ
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hπ
  have hρ : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hy0 : algebraMap E (Om l) ((minpoly E π).eval 0) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hρ _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow (hE ((minpoly E π).eval 0)) hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (N : ℤ)) = (l : ℝ) ^ (-((minpoly E π).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hπn, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (N : ℤ) = -((minpoly E π).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 (Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)).ne' h8
  have h10 : (N : ℤ) ∣ ((minpoly E π).natDegree : ℤ) := ⟨-m, by linarith⟩
  exact le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))

end GlobalTheory.InertiaDeg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeMinpolyRootNegPrimeUnramifiedStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (π : Om l), 0 < N → π ^ N = -(l : Om l) → ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → (minpoly E π).natDegree = N := by
  first | exact @GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l | exact GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l | (intros; apply GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedFieldOfMemMaxUnramifiedSupRoot

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.KunrDisj

theorem mem_Kunr_of_mem_Kur_of_mem_sup : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l →
    x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  intro l _ a e _ _ ϖ n x hxK hx
  have hN : 0 < l ^ n * e :=
    Nat.mul_pos (pow_pos (Fact.out : l.Prime).pos n) (Nat.pos_of_ne_zero (NeZero.ne e))
  have hπ : ϖ.seq n ^ (l ^ n * e) = -(l : Om l) := ϖ.seq_pow_mul n
  set U := Kunr l a with hU
  set π := ϖ.seq n with hπdef

  have hdeg := fun (E : Type) [Field E] [Algebra E (Om l)] (h : ∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) =>
    GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified l (l ^ n * e) π hN hπ E h
  have hint : ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) →
      IsIntegral E π := by
    intro E _ _ h
    by_contra hni
    have := hdeg E h
    rw [minpoly.eq_zero hni, Polynomial.natDegree_zero] at this
    omega
  let K2 : IntermediateField U (Om l) := IntermediateField.adjoin U {π}
  have hxK2 : x ∈ K2 := by
    have : x ∈ K2.restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact hx
    exact this
  let K1 : IntermediateField U (Om l) := IntermediateField.adjoin U {x}
  have hK1K2 : K1 ≤ K2 := IntermediateField.adjoin_simple_le_iff.2 hxK2
  have hUK : ∀ y : U, algebraMap U (Om l) y ∈ MaximalUnramifiedExtension l := fun y => Kunr_le_Kur l a y.2
  have hK1K : ∀ y : K1, algebraMap K1 (Om l) y ∈ MaximalUnramifiedExtension l := by
    intro y
    have hy : (y : Om l) ∈ K1.restrictScalars ℚ_[l] := y.2
    rw [IntermediateField.restrictScalars_adjoin] at hy
    refine (IntermediateField.adjoin_le_iff.2 ?_) hy
    rintro z (hz | hz)
    · exact Kunr_le_Kur l a hz
    · rw [Set.mem_singleton_iff.1 hz]; exact hxK

  let L : IntermediateField K1 (Om l) := IntermediateField.adjoin K1 {π}
  have hLK2 : L.restrictScalars U = K2 := by
    rw [IntermediateField.restrictScalars_adjoin]
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · exact hK1K2 hz
    · rw [Set.mem_singleton_iff.1 hz]; exact IntermediateField.mem_adjoin_simple_self U π
  have hK2r : Module.finrank U K2 = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint U hUK)]; exact hdeg U hUK
  have hLr : Module.finrank K1 L = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint K1 hK1K)]; exact hdeg K1 hK1K
  have hLU : Module.finrank U L = l ^ n * e := by
    rw [← hK2r, ← hLK2]; rfl
  have htower := Module.finrank_mul_finrank U K1 L
  rw [hLr, hLU] at htower
  have h1 : Module.finrank U K1 = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hN (htower.trans (one_mul _).symm)
    exact this
  have hbot : K1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  have : x ∈ K1 := IntermediateField.mem_adjoin_simple_self U x
  rw [hbot, IntermediateField.mem_bot] at this
  obtain ⟨y, rfl⟩ := this
  exact y.2

end GlobalTheory.KunrDisj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedFieldOfMemMaxUnramifiedSupRootStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l → x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  first | exact @GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | exact GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | (intros; apply GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingKunrMemInertiaModFieldInf

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaMod

open scoped Pointwise

variable {l : ℕ} [Fact l.Prime]

theorem ofGQ_apply (g : GQ l) (x : Om l) : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g x = g x := rfl

theorem Kur_stable (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : g x ∈ MaximalUnramifiedExtension l := by
  rw [← Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx ⊢
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Kur_stable (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l) (Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g) x hx
  rw [ofGQ_apply] at h
  exact h

theorem resid_of_fix (n : GQ l) (hn : ∀ x ∈ MaximalUnramifiedExtension l, n x = x) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖n x - x‖ < 1 := by
  have hmem : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ n ∈
      ReciprocityTheory.DiscreteGroups.LocalClassField.subG l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
        (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)) := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_iff]
    intro x hx
    rw [Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx
    rw [ofGQ_apply]
    exact hn x hx
  intro x hx
  have h := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
    Formalism.MainNotions.N.PreambleDegrees.Loc.finiteDimensional_Q0_alt _).1 hmem x hx
  rw [ofGQ_apply] at h
  exact h

theorem fix_Kur_normal : ((MaximalUnramifiedExtension l).fixingSubgroup : Subgroup (GQ l)).Normal := by
  constructor
  intro n hn τ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (Kur_stable τ⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

theorem mem_IK_of_fix (σ : GQ l) (hσ : ∀ x ∈ MaximalUnramifiedExtension l, σ x = x) :
    ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (k' : GQ l) = σ := by
  have hG : σ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact σ.commutes a
  exact ⟨⟨σ, hG⟩, Subgroup.subset_closure (fun x hx => resid_of_fix σ hσ x hx), rfl⟩

theorem exists_fix_Kur (M : IntermediateField ℚ_[l] (Om l)) (g : GQ l)
    (hg : ∀ x ∈ M, x ∈ MaximalUnramifiedExtension l → g x = x) :
    ∃ h ∈ M.fixingSubgroup, ∀ x ∈ MaximalUnramifiedExtension l, (g * h) x = x := by
  haveI := fix_Kur_normal (l := l)
  let S : Subgroup (GQ l) := M.fixingSubgroup ⊔ (MaximalUnramifiedExtension l).fixingSubgroup
  have hSc : IsClosed (S : Set (GQ l)) := by
    rw [Subgroup.mul_normal]
    exact IsClosed.mul_left_of_isCompact (InfiniteGalois.fixingSubgroup_isClosed _)
      (InfiniteGalois.fixingSubgroup_isClosed M).isCompact
  have hfS : (IntermediateField.fixedField S).fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨S, hSc⟩
  have hgS : g ∈ S := by
    rw [← hfS, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply hg
    · rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_left hσ)
    · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_right hσ)
  have hgNH : g ∈ ((M.fixingSubgroup : Set (GQ l)) * ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l))) := by
    rw [← Subgroup.mul_normal]; exact hgS
  obtain ⟨u, hu, n, hn, hun⟩ := Set.mem_mul.1 hgNH
  refine ⟨u⁻¹, M.fixingSubgroup.inv_mem hu, ?_⟩
  have hmem : g * u⁻¹ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    rw [← hun]
    exact (inferInstance : (MaximalUnramifiedExtension l).fixingSubgroup.Normal).conj_mem n hn u
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem

theorem seq_add_pow {e : ℕ} (ϖ : PiSys l e) (m k : ℕ) : ϖ.seq (m + k) ^ l ^ k = ϖ.seq m := by
  induction k with
  | zero => simp
  | succ k ih =>
    show ϖ.seq (m + k + 1) ^ l ^ (k + 1) = _
    rw [pow_succ', pow_mul, ϖ.seq_succ, ih]

theorem mem_level {a e : ℕ} [NeZero a] (ϖ : PiSys l e) {x : Om l} (hx : x ∈ ϖ.fieldInf a) :
    ∃ n, x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} := by
  let F : ℕ → IntermediateField ℚ_[l] (Om l) := fun n => Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n}
  have hs : ∀ n, ϖ.seq n ∈ F n := fun n =>
    (le_sup_right : _ ≤ F n) (IntermediateField.mem_adjoin_simple_self _ _)
  have hseq : ∀ m k, ϖ.seq m ∈ F (m + k) := by
    intro m k
    rw [← seq_add_pow ϖ m k]
    exact pow_mem (hs (m + k)) _
  have hmono : Monotone F := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact sup_le le_sup_left (IntermediateField.adjoin_simple_le_iff.2 (hseq m k))
  have hle : ϖ.fieldInf a ≤ ⨆ n, F n := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_trans le_sup_left (le_iSup F 0)
    · exact le_trans (IntermediateField.adjoin_simple_le_iff.2 (hs 0)) (le_iSup F 0)
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨n, rfl⟩
      exact le_iSup F n (hs n)
  have hx' : x ∈ ((⨆ n, F n : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hle hx
  rw [IntermediateField.coe_iSup_of_directed hmono.directed_le] at hx'
  exact Set.mem_iUnion.1 hx'

theorem fix_Kunr {a : ℕ} [NeZero a] (g : GQ l) (hg : ∀ x : Om l, x ^ l ^ a = x → g x = x) :
    ∀ x ∈ Kunr l a, g x = x := fun x hx => by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hg x hx
  | algebraMap r => exact g.commutes r
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a →
    ∀ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x) →
      ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ h ∈ ϖ.GfieldInf a, (k' : GQ l) = g * h := by
  intro l _ a e _ _ ϖ _ g hg
  obtain ⟨h, hh, hgh⟩ := exists_fix_Kur (ϖ.fieldInf a) g fun x hx hK => by
    obtain ⟨n, hn⟩ := mem_level ϖ hx
    exact fix_Kunr g hg x (GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root l a e ϖ n x hK hn)
  obtain ⟨k', hk', hkeq⟩ := mem_IK_of_fix (g * h) hgh
  exact ⟨k', hk', h, hh, hkeq⟩

end GlobalTheory.InertiaMod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingKunrMemInertiaModFieldInfStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.fixing_kunr_mem_inertia_mod_fieldInf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ h ∈ ϖ.GfieldInf a, (k' : GQ l) = g * h := by
  first | exact @GlobalTheory.InertiaMod.main | exact GlobalTheory.InertiaMod.main | (intros; apply GlobalTheory.InertiaMod.main <;> assumption)
end
end
