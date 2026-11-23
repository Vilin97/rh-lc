module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MarkWeightedFixedPointEqDefinitePairOdd
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FinitelyManyMarkedClassesTermDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMarkedPairClassesDegreeOneTermNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelBaseChangeMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkWeightedFixedPointDefinitePairOddOfCounts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplexCountRegularMarkedPoints
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceOfLefschetzAndGroupSide

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitelyManyMarkedClassesTermDegreeOne

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem commComm_conj {S : Type} [Ring S] (u : S) (v : Sˣ)
    (h : ∀ a b : S, Commute a u → Commute b u → Commute a b) :
    ∀ a b : S, Commute a (v * u * v⁻¹) → Commute b (v * u * v⁻¹) → Commute a b := by
  intro a b ha hb
  have key : ∀ c : S, Commute c (v * u * v⁻¹) → Commute (((v⁻¹ : Sˣ) : S) * c * v) u := by
    intro c hc
    unfold Commute SemiconjBy at hc ⊢
    calc (((v⁻¹ : Sˣ) : S) * c * v) * u = ((v⁻¹ : Sˣ) : S) * (c * (v * u * ((v⁻¹ : Sˣ) : S))) * v := by
          simp [mul_assoc]
      _ = ((v⁻¹ : Sˣ) : S) * ((v * u * ((v⁻¹ : Sˣ) : S)) * c) * v := by rw [hc]
      _ = u * (((v⁻¹ : Sˣ) : S) * c * v) := by simp [mul_assoc]
  have h' := h _ _ (key a ha) (key b hb)
  unfold Commute SemiconjBy at h' ⊢
  have := congrArg (fun z => (v : S) * z * ((v⁻¹ : Sˣ) : S)) h'
  simpa [mul_assoc] using this

variable {p : ℕ} [Fact p.Prime]

theorem regAf_conj (G : HTGroup p) (g h : G.GAf) (hg : RegAf G g) : RegAf G (h⁻¹ * g * h) := by
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  have e : ((ubcMap (AfP.eval w) (h⁻¹ * g * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (((ubcMap (AfP.eval w) h).1.1⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((((ubcMap (AfP.eval w) h).1.1⁻¹)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    simp [map_mul, map_inv]
  rw [e]
  exact commComm_conj _ _ hw

theorem commComm_tmul (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (γ : G.C)
    (hsep : (minpoly G.F γ).Separable) (hdeg : (minpoly G.F γ).natDegree = G.n) :
    ∀ a b : K ⊗[ℚ] G.C, Commute a ((1 : K) ⊗ₜ γ) → Commute b ((1 : K) ⊗ₜ γ) → Commute a b := by
  set Z := Subalgebra.centralizer ℚ ({γ} : Set G.C) with hZdef
  have hZ : ∀ x y : Z, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC γ hsep hdeg
    have hx : ∀ g ∈ ({γ} : Set G.C), g * (x : G.C) = x * g := (Subalgebra.mem_centralizer_iff _).1 x.2
    have hy : ∀ g ∈ ({γ} : Set G.C), g * (y : G.C) = y * g := (Subalgebra.mem_centralizer_iff _).1 y.2
    show (x : G.C) * y = y * x
    have hy' : (y : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hy
    rw [hc] at hy'
    have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({γ} : Set G.C) hy'
    rw [Subalgebra.mem_centralizer_iff] at h2
    have hx' : (x : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hx
    exact h2 x hx'
  have hcomm : ∀ a b : K ⊗[ℚ] Z, a * b = b * a := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    | tmul r x =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
      | tmul s y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm r s, hZ x y]
  have hcen := Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct ℚ K G.C ({γ} : Set G.C)
  have mem : ∀ c : K ⊗[ℚ] G.C, Commute c ((1 : K) ⊗ₜ γ) →
      c ∈ (Algebra.TensorProduct.map (AlgHom.id ℚ K) Z.val).range := by
    intro c hc
    rw [← hcen, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hc.eq.symm
  intro a b ha hb
  obtain ⟨a', rfl⟩ := mem a ha
  obtain ⟨b', rfl⟩ := mem b hb
  unfold Commute SemiconjBy
  rw [← map_mul, ← map_mul, hcomm]

theorem regAf_pair (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (h : G.GAf) : RegAf G (h⁻¹ * P.toAf x t hx P.self * h) := by
  apply regAf_conj
  obtain ⟨w⟩ := finitePlacesAway_nonempty p
  refine ⟨w, ?_⟩
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  have e : ((ubcMap (AfP.eval w) (P.toAf x t hx P.self)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      ((Units.map φ.toRingHom.toMonoidHom x : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((1 : w.1.adicCompletion ℚ) ⊗ₜ (P.γ : G.C)) *
        (((Units.map φ.toRingHom.toMonoidHom x)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (P.γ : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
    rw [map_mul, map_mul]
    simp [φ, inC, Units.coe_map_inv]
  rw [e]
  exact commComm_conj _ _ (commComm_tmul G _ _ P.reg.2 P.reg.1)

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem finitely_many_marked_classes_degree_one_of_regular (hI : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    Set.Finite {Q : Cls G | (∃ μ, (Quot.out Q).Mark μ) ∧ (Quot.out Q).term L.K.toSubgroup f 1 K' f' ≠ 0}) :
    GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := by
  intro p _ G ha L f K' f' hf hf'
  let f₀ : G.GAf → ℂ := fun g => if RegAf G g then f g else 0
  have hiff : ∀ (k g : G.GAf), RegAf G (k⁻¹ * g * k) ↔ RegAf G g := by
    intro k g
    refine ⟨fun h => ?_, fun h => regAf_conj G g k h⟩
    have := regAf_conj G _ k⁻¹ h
    simpa [mul_assoc] using this
  have hf₀ : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f₀ := by
    obtain ⟨h1, h2, h3, S, hS⟩ := hf
    refine ⟨h1, h2, fun k hk g => ?_, S, fun g hg => hS g ?_⟩
    · have e := h3 k hk g
      simp only [MonoidHom.id_apply] at e ⊢
      simp only [f₀, e, hiff]
    · intro h; apply hg; simp [f₀, h]
  have hreg : ∀ g, f₀ g ≠ 0 → RegAf G g := fun g hg => by
    by_contra h; exact hg (by simp [f₀, h])
  have hterm : ∀ P : Pair G, P.term L.K.toSubgroup f 1 K' f' = P.term L.K.toSubgroup f₀ 1 K' f' := by
    intro P
    have key : ∀ x t hx δ z, P.termAt L.K.toSubgroup f 1 K' f' x t hx δ z =
        P.termAt L.K.toSubgroup f₀ 1 K' f' x t hx δ z := by
      intro x t hx δ z
      unfold Pair.termAt pointSum
      refine finsum_congr fun q => ?_
      have : f ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) =
          f₀ ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) := by
        simp only [f₀, if_pos (regAf_pair G P x t hx _)]
      rw [this]
    unfold Pair.term
    split_ifs <;> simp only [key]
  have hfin := hI p G ha L f₀ hf₀ hreg K' f' hf'
  simpa only [hterm] using hfin

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem GlobalTheory.RootSumWeights.finitely_many_marked_classes_term_degree_one : GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas.finitely_many_marked_classes_degree_one_of_regular GlobalTheory.T.finite_markedPairClasses_degreeOne_term_ne_zero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumReindexEquivalentSubtypes

section

@[expose] public section

open scoped Classical

namespace GlobalTheory

theorem finsum_ite_eq_of_equiv {A B : Type} (PA : A → Prop) (PB : B → Prop)
    (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ)
    (hgh : ∀ a, h (e a).1 = g a.1) :
    (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 := by
  have hA : (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ a : {a // PA a}, g a.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun a => (finsum_eq_if).symm
  have hB : (∑ᶠ b, if PB b then h b else 0) = ∑ᶠ b : {b // PB b}, h b.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun b => (finsum_eq_if).symm
  rw [hA, hB, ← finsum_comp_equiv e]
  exact finsum_congr fun a => (hgh a).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOddStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  first | (exact @GlobalTheory.LKDef.cls_equiv_dcls_irr) | (exact GlobalTheory.LKDef.cls_equiv_dcls_irr) | (intros; apply GlobalTheory.LKDef.cls_equiv_dcls_irr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsSumEqDefinitePairsSum

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem marked_field_pairs_sum_eq_definite_pairs_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ := by
  intro p _ G ha hn wt sel hsel Kf f r K φ hr hf hφ
  obtain ⟨e, he⟩ := GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd p G ha hn sel hsel
  unfold markedSumIrr dSumIrr
  convert GlobalTheory.finsum_ite_eq_of_equiv _ _ e (fun a : Cls G => wt (Quot.out a).pol * (Quot.out a).term Kf f r K φ)
    (fun b : DCls G => wt (Quot.out b).pol * (Quot.out b).term Kf f r K φ) fun q => by
    obtain ⟨hpol, hterm⟩ := he q
    show wt (Quot.out (e q).1).pol * (Quot.out (e q).1).term Kf f r K φ = wt (Quot.out q.1).pol * (Quot.out q.1).term Kf f r K φ
    rw [hpol, hterm Kf f r K φ hr hf hφ]

end GlobalTheory.LKDef
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.DefiniteTraceForms.WeightedCountDefiniteUnitary

section

@[expose] public section

namespace UpperTheory.Gal.Cnt

theorem weighted_count_definite_unitary : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd :=
  GlobalTheory.RootSumWeights.markWeightedFixedPoint_definitePair_odd_of_counts GlobalTheory.LKDef.marked_field_pairs_sum_eq_definite_pairs_sum UpperTheory.Cb.complex_count_regular_marked_points GlobalTheory.RootSumWeights.finitely_many_marked_classes_term_degree_one

theorem trace_definite_forms_identity : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace := GlobalTheory.LKDef.trace_definite_forms_identity

end UpperTheory.Gal.Cnt
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.KsHodgeOfGeo

section

@[expose] public section

namespace UpperTheory.Gal.LocalSmoothExtension

theorem ksHodge_of_geo (hW : HolomorphicLefschetzFormula) (hF : FixK) : UpperTheory.Gal.Int.Geo.KSHodge :=
  ksHodge_of_inputs hW hF UpperTheory.Gal.Cnt.weighted_count_definite_unitary UpperTheory.Gal.Cnt.trace_definite_forms_identity

end UpperTheory.Gal.LocalSmoothExtension
end
end
