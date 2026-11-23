module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFieldCharacterLabelsCompatNormPowInvStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitRootPolynomialFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductList
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledCharactersEqAndCongrPrimeToPart
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackeyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParamStatement

section

@[expose] public section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.greenCuspidalChar_isCuspidalOfMinpoly_of_param : GlobalTheory.GLq.Green → ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p), 5 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p), 0 < Fintype.card ι → LabelsChar L θ x → (minpoly (ZMod p) x).natDegree = Fintype.card ι → GlobalTheory.GLq.IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) := by
  first | exact @GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green | exact GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green | (intros; apply GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductListStatement

section

@[expose] public section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.harishChandraInducedTypeChar_eq_productList : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (s : SSParam p ℂ r), ∃ l : List (Cyc s.1), l.Nodup ∧ (∀ c, c ∈ l) ∧ typeChar s = GlobalTheory.GLq.hcL (l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p)) r := by
  first | exact @GlobalTheory.TypeCharProduct.typeChar_eq_hcL | exact GlobalTheory.TypeCharProduct.typeChar_eq_hcL | (intros; apply GlobalTheory.TypeCharProduct.typeChar_eq_hcL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledCharactersEqAndCongrPrimeToPartStatement

section

@[expose] public section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (d : ℕ), 0 < d → ∀ (θ θ' : Tor p d →* ℂˣ) (x x' : Fbar p), LabelsChar L θ x → LabelsChar L θ' x' → (θ = θ' ↔ x = x') ∧ ∀ l : ℕ, l.Prime → (CongrMod l θ θ' ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l x') := by
  first | exact @GlobalTheory.ParamLabel.Congr.eq_and_congr | exact GlobalTheory.ParamLabel.Congr.eq_and_congr | (intros; apply GlobalTheory.ParamLabel.Congr.eq_and_congr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeDivisorsProdDistinctMonicIrreducible

section

@[expose] public section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible

theorem exists_subset_natDegree_of_dvd_prod {k : Type} [Field k] {ι : Type} (P : ι → k[X])
    (hP : ∀ c, Irreducible (P c)) (s : Finset ι) :
    ∀ q : k[X], q ∣ ∏ c ∈ s, P c → ∃ A : Finset ι, A ⊆ s ∧ ∑ c ∈ A, (P c).natDegree = q.natDegree := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro q hq
    rw [Finset.prod_empty] at hq
    exact ⟨∅, Finset.Subset.refl _, by
      rw [Finset.sum_empty, natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hq)]⟩
  | insert i s hi ih =>
    intro q hq
    have hne : ∏ c ∈ insert i s, P c ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun c _ => (hP c).ne_zero
    have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero hne hq
    rw [Finset.prod_insert hi] at hq
    obtain ⟨q₁, q₂, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hq
    obtain ⟨A, hA, hsum⟩ := ih q₂ h2
    have hq1 : q₁ ≠ 0 := left_ne_zero_of_mul hq0
    have hq2 : q₂ ≠ 0 := right_ne_zero_of_mul hq0
    rw [natDegree_mul hq1 hq2]
    rcases (hP i).dvd_iff.mp h1 with hu | ha
    · exact ⟨A, hA.trans (Finset.subset_insert _ _), by
        rw [hsum, natDegree_eq_zero_of_isUnit hu, zero_add]⟩
    · refine ⟨insert i A, Finset.insert_subset_insert _ hA, ?_⟩
      rw [Finset.sum_insert (fun h => hi (hA h)), hsum,
        natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]

theorem natDegree_divisors_prod :
    ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  intro k _ ι _ P hP _
  refine ⟨fun a => ⟨?_, ?_⟩, fun Q => ⟨?_, ?_⟩⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨A, -, hA⟩ := exists_subset_natDegree_of_dvd_prod P (fun c => (hP c).2) _ q hq
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    exact ⟨∏ c ∈ A, P c, Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _),
      natDegree_prod_of_monic _ _ fun c _ => (hP c).1⟩
  · rintro ⟨q, hirr, hq, hQ⟩
    obtain ⟨c, -, hc⟩ := (Prime.dvd_finsetProd_iff hirr.prime _).mp hq
    have ha := hirr.associated_of_dvd (hP c).2 hc
    refine ⟨c, ?_⟩
    rwa [← natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]
  · rintro ⟨c, hc⟩
    exact ⟨P c, (hP c).2, Finset.dvd_prod_of_mem _ (Finset.mem_univ c), hc⟩

end GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeDivisorsProdDistinctMonicIrreducibleStatement

section

@[expose] public section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  first | exact @GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | exact GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | (intros; apply GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToPartFrob

section

@[expose] public section

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

theorem bb_eq (p r : ℕ) : BB p r = Formalism.CyclotomicNorms.BB r p := by
  ext l
  simp only [BB, Formalism.CyclotomicNorms.BB, Formalism.CyclotomicNorms.Exc, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, ← pow_mul, mul_comm 4]
  refine or_congr_right ⟨fun ⟨h, a, h1, h2, h3⟩ => ⟨a, h1, h2, h, h3⟩, fun ⟨a, h1, h2, h, h3⟩ => ⟨h, a, h1, h2, h3⟩⟩

theorem primeToPart_frob (l i : ℕ) (z : Fbar p) (a : ZMod p) :
    Formalism.CyclotomicNorms.primeToPart l (z ^ p ^ i) = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) ↔
      Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) := by
  let β : Fbar p ≃* Fbar p := (iterateFrobeniusEquiv (Fbar p) p i).toMulEquiv
  have h1 : z ^ p ^ i = β z := rfl
  have h2 : β (algebraMap (ZMod p) (Fbar p) a) = algebraMap (ZMod p) (Fbar p) a := by
    show algebraMap (ZMod p) (Fbar p) a ^ p ^ i = _
    rw [← map_pow, ZMod.pow_card_pow]
  conv_lhs => rw [h1, ← h2, GlobalTheory.GoodCharsCompare.primeToPart_map, GlobalTheory.GoodCharsCompare.primeToPart_map]
  exact β.injective.eq_iff

section Good

variable {L : GlobalTheory.GLq.LabelDatum p} {r : ℕ} {s : SSParam p ℂ r} {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]}

theorem Labels.root (h : Labels L s x f) (y) : LabelsChar L (rootChar s y) (rootElt x y) :=
  (GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 y.1) _ _ _ (h.1 y.1)

theorem Labels.cyc (h : Labels L s x f) (c) : LabelsChar L (cycChar s c) (x c) := by
  have := (GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 c) _ _ 1 (h.1 c)
  rwa [pow_one, pow_one] at this

theorem Labels.mem_roots (h : Labels L s x f) (z : Fbar p) : z ∈ Formalism.CyclotomicNorms.rootsBar f ↔ ∃ y, rootElt x y = z := by
  rw [h.2.2.2]; simp

theorem Labels.regular_iff (h : Labels L s x f) : IsRegularParam s ↔ Squarefree f := by
  rw [(GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1]
  exact forall₂_congr fun y y' => by
    rw [(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).1]

theorem Labels.two_iff (h : Labels L s x f) (hs : Squarefree f) {l : ℕ} (hl : l.Prime) :
    (∀ y y', y ≠ y' → ¬ CongrMod l (rootChar s y) (rootChar s y')) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, ∀ z' ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l z' → z = z' := by
  have hi := (GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1.1 hs
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, hi.eq_iff]
  exact forall₂_congr fun y y' => by
    rw [(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).2 l hl, not_imp_not]

theorem Labels.three_iff (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a)
    {l : ℕ} (hl : l.Prime) :
    (∀ c, ¬ CongrMod l (cycChar s c) (χ.comp (baseNorm p r.factorial))) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have hχ := ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, rootElt, Ne, primeToPart_frob,
    (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.cyc _) hχ).2 l hl]
  exact ⟨fun H y => H y.1, fun H c => H ⟨c, ⟨0, cycLen_pos _ c⟩⟩⟩

theorem Labels.ne_of (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a) {l : ℕ}
    (H : ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p))) (y) :
    rootChar s y ≠ χ.comp (baseNorm p r.factorial) := fun e => by
  have hχ := ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1
  have := (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) hχ).1.1 e
  exact H _ ((h.mem_roots _).2 ⟨y, rfl⟩) (by rw [this])

theorem Labels.dvd_iff (h : Labels L s x f) (hs : Squarefree f) :
    (∀ a : ℕ, (∃ q : (ZMod p)[X], q ∣ f ∧ q.natDegree = a) ↔ ∃ A : Finset (Cyc s.1), ∑ c ∈ A, cycLen s.1 c = a) ∧
    ∀ Q : ℕ → Prop, (∃ q : (ZMod p)[X], Irreducible q ∧ q ∣ f ∧ Q q.natDegree) ↔ ∃ c, Q (cycLen s.1 c) := by
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.2 hs
  have := GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible (ZMod p) _ _ (fun c => ⟨minpoly.monic (Algebra.IsIntegral.isIntegral (x c)),
    minpoly.irreducible (Algebra.IsIntegral.isIntegral (x c))⟩) h2
  simp only [h1, ← h3] at this
  exact this

end Good

theorem good_iff (L : GlobalTheory.GLq.LabelDatum p) (h5 : 5 ≤ p) {r : ℕ} {ι J : Type} (s : ι → SSParam p ℂ r)
    (x : ∀ v, Cyc (s v).1 → Fbar p) (f : ι → (ZMod p)[X]) (h : ∀ v, Labels L (s v) (x v) (f v))
    (χ : J → (ZMod p)ˣ →* ℂˣ) (a : ι → J → (ZMod p)ˣ)
    (ha : ∀ v j, LabelsTame L (χ j) (a v j) ∨ LabelsTame L (χ j)⁻¹ (a v j)) :
    GoodAt χ s ↔ Formalism.CyclotomicNorms.IsGood r p f a ∧ Formalism.CyclotomicNorms.IsGood r p f fun v j => (a v j)⁻¹ := by
  have inv : ∀ {χ : (ZMod p)ˣ →* ℂˣ} {a}, LabelsTame L χ a → LabelsTame L χ⁻¹ a⁻¹ := fun h =>
    ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L 1 one_pos).2 _ _ h).2
  have three : ∀ l : ℕ, l.Prime → ∀ v j,
      ((∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j).comp (baseNorm p r.factorial))) ∧
        ∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j)⁻¹.comp (baseNorm p r.factorial))) ↔
      (∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a v j : ZMod p))) ∧
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) ((a v j)⁻¹ : (ZMod p)ˣ)) := by
    intro l hl v j
    rcases ha v j with H | H
    · rw [(h v).three_iff H hl, (h v).three_iff (inv H) hl]
    · have H' := inv H
      rw [inv_inv] at H'
      rw [(h v).three_iff H hl, (h v).three_iff H' hl, and_comm]
  have base := fun v => GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ (x v) (f v) (h v).2
  constructor
  · rintro ⟨g1, g2, ⟨g3, -⟩, g4, g5⟩
    have hs := fun v => (h v).regular_iff.1 (g1 v)
    have k3 := fun l hl hp v j => (three l hl v j).1 ⟨fun c => (g3 l hl hp v j c).1, fun c => (g3 l hl hp v j c).2⟩
    have key : ∀ a' : ι → J → (ZMod p)ˣ, (∀ l : ℕ, l.Prime → l ≠ p → ∀ v j, ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v),
        Formalism.CyclotomicNorms.primeToPart l z ≠ Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a' v j : ZMod p))) →
        Formalism.CyclotomicNorms.IsGood r p f a' := fun a' H => by
      refine ⟨fun v => ⟨(h v).2.2.1, (base v).1, (base v).2.1⟩, hs,
        fun l hl hb v => ((h v).two_iff (hs v) hl).1 (g2 l hl (bb_eq p r ▸ hb) v), H, fun n h1 h2 => ?_, ?_⟩
      · by_contra hc
        push Not at hc
        exact g4 ⟨n, h1, h2, fun v => (((h v).dvd_iff (hs v)).1 n).1 (hc v)⟩
      · obtain ⟨v, hv⟩ := g5
        exact ⟨v, (((h v).dvd_iff (hs v)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).2 hv⟩
    exact ⟨key _ fun l hl hp v j => (k3 l hl hp v j).1, key _ fun l hl hp v j => (k3 l hl hp v j).2⟩
  · rintro ⟨⟨-, hs, g2, g3, g4, v₀, g5⟩, -, -, -, g3', -⟩
    have k3 := fun l hl hp v j => (three l hl v j).2 ⟨g3 l hl hp v j, g3' l hl hp v j⟩
    refine ⟨fun v => (h v).regular_iff.2 (hs v), fun l hl hb v => ((h v).two_iff (hs v) hl).2 (g2 l hl (bb_eq p r ▸ hb) v),
      ⟨fun l hl hp v j c => ⟨(k3 l hl hp v j).1 c, (k3 l hl hp v j).2 c⟩, fun v j y => ?_⟩, ?_,
      v₀, (((h v₀).dvd_iff (hs v₀)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).1 g5⟩
    · have e1 := g3 2 Nat.prime_two (by omega) v j
      have e2 := g3' 2 Nat.prime_two (by omega) v j
      rcases ha v j with H | H
      · exact ⟨(h v).ne_of H e1 y, (h v).ne_of (inv H) e2 y⟩
      · have H' := inv H
        rw [inv_inv] at H'
        exact ⟨(h v).ne_of H' e2 y, (h v).ne_of H e1 y⟩
    · rintro ⟨n, h1, h2, H⟩
      obtain ⟨v, hv⟩ := g4 n h1 h2
      exact hv ((((h v).dvd_iff (hs v)).1 n).2 (H v))

theorem Labels.series (hG : GlobalTheory.GLq.Green) {L : GlobalTheory.GLq.LabelDatum p} (h5 : 5 ≤ p) {r : ℕ} {s : SSParam p ℂ r}
    {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]} (h : Labels L s x f) (hs : Squarefree f) :
    {χ | GlobalTheory.GLq.IsIrr χ ∧ GlobalTheory.GLq.HasLabel L χ f} = {typeChar s} ∧
      GlobalTheory.GLq.eSerC L r f = centralIdem (typeChar s) := by
  obtain ⟨d1, d2, -, d3⟩ := GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2
  obtain ⟨h1, h2, h3⟩ := d3 hs
  obtain ⟨l, hl, hl', e⟩ := GlobalTheory.T.harishChandraInducedTypeChar_eq_productList p r s
  let Q : List ((ZMod p)[X] × GlobalTheory.GLq.Pc p) := l.map fun c => (minpoly (ZMod p) (x c), ⟨cycLen s.1 c, cuspOn (s.2 c)⟩)
  have hsnd : Q.map Prod.snd = l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p) := by
    rw [List.map_map]; rfl
  have hfst : Q.map Prod.fst = l.map fun c => minpoly (ZMod p) (x c) := by
    rw [List.map_map]; rfl
  have hQ : ∀ q ∈ Q, GlobalTheory.GLq.IsCuspOf L q.1 q.2.2 := by
    intro q hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    exact GlobalTheory.T.greenCuspidalChar_isCuspidalOfMinpoly_of_param hG p L h5 _ (s.2 c) (x c) (cycLen_pos _ c) (h.1 c) (h1 c)
  have hprod : f = (Q.map Prod.fst).prod := by
    classical
    rw [hfst, h3, ← List.prod_toFinset _ hl]
    congr 1
    exact (Finset.eq_univ_of_forall fun c => List.mem_toFinset.2 (hl' c)).symm
  have hdeg : GlobalTheory.GLq.degL (Q.map Prod.snd) = r := by
    rw [← (GlobalTheory.GLq.Label.prod_props L Q hQ).2.1, ← hprod, d1]
  have hnd : (Q.map Prod.snd).Nodup := by
    apply List.Nodup.of_map (GlobalTheory.GLq.Label.lab L)
    rw [← GlobalTheory.GLq.Label.map_fst_eq L h5 Q hQ, hfst]
    exact hl.map h2
  rw [← hsnd] at e
  have hip := (GlobalTheory.T.characterPairing_harishChandra_cuspidal_mackey p _ _ r hdeg hdeg (GlobalTheory.GLq.Label.cusp_snd L Q hQ) (GlobalTheory.GLq.Label.cusp_snd L Q hQ)).2 hnd
  have hirr : GlobalTheory.GLq.IsIrr (typeChar s) :=
    e ▸ (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant p _ [] r hdeg.symm (GlobalTheory.GLq.Label.char_snd L Q hQ)).1 hip
  have hlab : GlobalTheory.GLq.HasLabel L (typeChar s) f := ⟨Q, hQ, hdeg, hprod, by rw [e, hip]; exact one_ne_zero⟩
  obtain ⟨Q', -, -, -, hset⟩ := GlobalTheory.GLq.Label.squarefree_series L h5 hG r f h.2.2.1 d1 d2 hs
  have : typeChar s = GlobalTheory.GLq.hcL (Q'.map Prod.snd) r := by
    rw [← Set.mem_singleton_iff, ← hset]; exact ⟨hirr, hlab⟩
  refine ⟨this ▸ hset, ?_⟩
  unfold GlobalTheory.GLq.eSerC
  rw [hset, finsum_mem_singleton, ← this]
  unfold GlobalTheory.GLq.zOf centralIdem
  rw [Nat.card_eq_fintype_card]
  convert rfl

end GlobalTheory.ParamLabel

end
end
end
