module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.AnnAnti
public import Mathlib.GroupTheory.Index
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
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLattice
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.MirabolicVectors.ContinuousMulVec
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.TransversalSums.ContinuousBlkAtApply
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.TransversalSums.SumTranslateTransversal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCosetRepsEqRelIndex

section

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

theorem card_eq_relIndex (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X)
    (_hLA : L ≤ A) (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) :
    T.card = L.relIndex A := by
  classical
  let f : T → A ⧸ L.addSubgroupOf A := fun t => QuotientAddGroup.mk ⟨t.1, hT t.1 t.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h' : -(⟨t, hT t ht⟩ : A) + ⟨t', hT t' ht'⟩ ∈ L.addSubgroupOf A := QuotientAddGroup.eq.mp h
      rw [AddSubgroup.mem_addSubgroupOf] at h'
      have hL : t - t' ∈ L := by
        have h2 := L.neg_mem h'
        convert h2 using 1
        push_cast
        abel
      obtain ⟨u, _, hu'⟩ := hu t (hT t ht)
      have e1 : t = u := hu' t ⟨ht, by simp⟩
      have e2 : t' = u := hu' t' ⟨ht', hL⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨t, ⟨ht, hat⟩, _⟩ := hu a.1 a.2
      refine ⟨⟨t, ht⟩, QuotientAddGroup.eq.mpr ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have e : ((-(⟨t, hT t ht⟩ : A) + a : A) : X) = a.1 - t := by
        push_cast
        abel
      rw [e]
      exact hat
  calc T.card = Nat.card T := (Nat.card_eq_finsetCard T).symm
    _ = Nat.card (A ⧸ L.addSubgroupOf A) := Nat.card_congr (Equiv.ofBijective f hf)
    _ = L.relIndex A := by simp only [AddSubgroup.relIndex, AddSubgroup.index]

end GlobalTheory.CompanionTheory.Transversal
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCosetRepsEqRelIndexStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.card_coset_reps_eq_relIndex : ∀ (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X), L ≤ A → (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) → T.card = L.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | exact GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | (intros; apply GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLatticeStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_character_separating_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A → ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | exact GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | (intros; apply GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCosetRepsOpenInCompact

section

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.Topology

theorem exists_finset_transversal_of_isCompact_of_isOpen
    (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (A L : AddSubgroup X) (hA : IsCompact (A : Set X)) (hL : IsOpen (L : Set X)) (_hLA : L ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  classical
  have hcoset : ∀ x : X, ((↑) : X → X ⧸ L) '' (Homeomorph.addLeft x '' (L : Set X)) =
      {(x : X ⧸ L)} := by
    intro x
    ext q
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff, QuotientAddGroup.eq, Homeomorph.coe_addLeft]
      simpa using L.neg_mem hl
    · rintro rfl
      exact ⟨x, ⟨0, L.zero_mem, by simp⟩, rfl⟩
  have hdisc : DiscreteTopology (X ⧸ L) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← hcoset x]
      exact QuotientAddGroup.isOpenMap_coe _ ((Homeomorph.addLeft x).isOpenMap _ hL)
  have hfin : (((↑) : X → X ⧸ L) '' (A : Set X)).Finite :=
    (hA.image continuous_quotient_mk').finite_of_discrete
  have hout : ∀ q : X ⧸ L, ((q.out : X) : X ⧸ L) = q := fun q => Quotient.out_eq q
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := ht
    have h1 : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    have h2 : (a : X ⧸ L).out = a - (-(a : X ⧸ L).out + a) := by abel
    rw [h2]
    exact A.sub_mem ha (_hLA h1)
  · intro a ha
    have hmem : (a : X ⧸ L).out ∈ hfin.toFinset.image Quotient.out :=
      Finset.mem_image.2 ⟨(a : X ⧸ L), (Set.Finite.mem_toFinset hfin).2 ⟨a, ha, rfl⟩, rfl⟩
    have hrel : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    refine ⟨(a : X ⧸ L).out, ⟨hmem, by rw [sub_eq_neg_add]; exact hrel⟩, ?_⟩
    rintro t' ⟨ht', hat'⟩
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht'
    obtain ⟨q', -, rfl⟩ := ht'
    have hq : q' = (a : X ⧸ L) := by
      rw [← hout q', QuotientAddGroup.eq]
      rw [sub_eq_neg_add] at hat'
      exact hat'
    rw [hq]

end GlobalTheory.CompanionTheory.Topology
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCosetRepsOpenInCompactStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_coset_reps_open_in_compact : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (A L : AddSubgroup X), IsCompact (A : Set X) → IsOpen (L : Set X) → L ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.ConjCircleEqOne

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_tr_indep {X W : Type} [AddCommGroup X] [AddCommMonoid W] (A L : AddSubgroup X) (T T' : Finset X)
    (hT : IsTr A L T) (hT' : IsTr A L T') (F : X → W) (hF : ∀ a, ∀ d ∈ L, F (a + d) = F a) :
    ∑ t ∈ T, F t = ∑ t ∈ T', F t := by
  classical
  have hσ : ∀ t ∈ T, ∃ s, s ∈ T' ∧ t - s ∈ L := fun t ht => (hT'.2 t (hT.1 t ht)).exists
  have hτ : ∀ s ∈ T', ∃ t, t ∈ T ∧ s - t ∈ L := fun s hs => (hT.2 s (hT'.1 s hs)).exists
  choose! σ hσT hσL using hσ
  choose! τ hτT hτL using hτ
  refine Finset.sum_nbij' σ τ hσT hτT ?_ ?_ ?_
  · intro t ht
    refine (hT.2 t (hT.1 t ht)).unique ⟨hτT _ (hσT t ht), ?_⟩ ⟨ht, by simp⟩
    have e : t - τ (σ t) = (t - σ t) + (σ t - τ (σ t)) := by abel
    rw [e]; exact L.add_mem (hσL t ht) (hτL _ (hσT t ht))
  · intro s hs
    refine (hT'.2 s (hT'.1 s hs)).unique ⟨hσT _ (hτT s hs), ?_⟩ ⟨hs, by simp⟩
    have e : s - σ (τ s) = (s - τ s) + (τ s - σ (τ s)) := by abel
    rw [e]; exact L.add_mem (hτL s hs) (hσL _ (hτT s hs))
  · intro t ht
    have := hF (σ t) _ (hσL t ht)
    rw [← this]; congr 1; abel

theorem isTr_filter {X : Type} [AddCommGroup X] (A A' H : AddSubgroup X) (hHA : H ≤ A) (U : Finset X)
    (hU : IsTr A' H U) (hAA : A ≤ A') [DecidablePred (· ∈ A)] : IsTr A H (U.filter (· ∈ A)) := by
  refine ⟨fun t ht => (Finset.mem_filter.1 ht).2, fun a ha => ?_⟩
  obtain ⟨u, ⟨hu, hau⟩, huniq⟩ := hU.2 a (hAA ha)
  have huA : u ∈ A := by
    have e : u = a - (a - u) := by abel
    rw [e]; exact A.sub_mem ha (hHA hau)
  refine ⟨u, ⟨Finset.mem_filter.2 ⟨hu, huA⟩, hau⟩, fun t ⟨ht, hat⟩ => huniq t ⟨(Finset.mem_filter.1 ht).1, hat⟩⟩

theorem conj_circle_eq_one {z : Circle} (hz : z = 1) : starRingEnd ℂ (z : ℂ) = 1 := by simp [hz]

theorem sum_char {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ}
    {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {R : Finset (Fin (m + 1) → k)}
    (hR : IsTr (ann ψ A) (ann ψ A') R) (u : Fin (m + 1) → k) (hu : u ∈ A') [Decidable (u ∈ A)] :
    ∑ η ∈ R, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) = if u ∈ A then (R.card : ℂ) else 0 := by
  split_ifs with huA
  · rw [Finset.sum_congr rfl fun η hη => conj_circle_eq_one (hR.1 η hη u huA), Finset.sum_const, nsmul_eq_mul,
      mul_one]
  · obtain ⟨η₀, hη₀A, hη₀u⟩ := GlobalTheory.T.exists_character_separating_lattice k ψ hψ hψ1 (m + 1) A hA.1 hA.2 u huA
    set F : (Fin (m + 1) → k) → ℂ := fun η => starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) with hFdef
    have hF : ∀ a, ∀ d ∈ ann ψ A', F (a + d) = F a := by
      intro a d hd
      simp only [hFdef, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul, hd u hu, Circle.coe_one,
        map_one, mul_one]
    have e := sum_translate_transversal (ann ψ A) (ann ψ A') R hR.1 hR.2 F hF η₀ hη₀A
    have e2 : ∀ η, F (η + η₀) = F η * starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) := by
      intro η
      simp only [hFdef, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    simp only [e2, ← Finset.sum_mul] at e
    have hc : starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) ≠ 1 := by
      intro hc
      apply hη₀u
      have : ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) = 1 := by
        have := congrArg (starRingEnd ℂ) hc
        simpa using this
      exact Circle.coe_inj.1 (by simpa using this)
    have : (∑ η ∈ R, F η) * (starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) - 1) = 0 := by
      rw [mul_sub, mul_one, e, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hc)

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V}

theorem avg_decomp_pf (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') (hAA : A ≤ A') {R T : Finset (Fin (m + 1) → k)}
    (hR : IsTr (ann ψ A) (ann ψ A') R) (hT : IsTr A' A T) (v : V) :
    (R.card : ℂ) • avg ψ h π ξ A v = (T.card : ℂ) • ∑ η ∈ R, avg ψ h π (ξ + η) A' v := by
  classical
  obtain ⟨⟨H, S⟩, hHA, hHo, hHv, hHξ, hS1, hS2⟩ := avgData_exists ψ h π hψ hπ ξ A hA v
  obtain ⟨U, hU1, hU2⟩ := GlobalTheory.T.exists_coset_reps_open_in_compact (Fin (m + 1) → k) A' H hA'.1 hHo (hHA.trans hAA)
  set f : (Fin (m + 1) → k) → V := fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v
    with hfdef

  have hav : avg ψ h π ξ A v = ((S.card : ℂ)⁻¹) • ∑ t ∈ S, f t :=
    PositivityTheory.RgUd.Form.LeviSmoothness.mir.avg_eq_of_data ψ h π hψ hπ ξ hA v ⟨H, S⟩ ⟨hHA, hHo, hHv, hHξ, hS1, hS2⟩
  have hav' : ∀ η ∈ R, avg ψ h π (ξ + η) A' v =
      ((U.card : ℂ)⁻¹) • ∑ u ∈ U, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) • f u := by
    intro η hη
    have hdat : AvgData ψ h π (ξ + η) A' v ⟨H, U⟩ := by
      refine ⟨hHA.trans hAA, hHo, hHv, fun a ha => ?_, hU1, hU2⟩
      rw [add_dotProduct, AddChar.map_add_eq_mul, hHξ a ha, hR.1 η hη a (hHA ha), one_mul]
    rw [PositivityTheory.RgUd.Form.LeviSmoothness.mir.avg_eq_of_data ψ h π hψ hπ (ξ + η) hA' v ⟨H, U⟩ hdat]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hfdef, smul_smul, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    ring_nf

  have hsum : ∑ η ∈ R, avg ψ h π (ξ + η) A' v = ((U.card : ℂ)⁻¹ * (R.card : ℂ)) • ∑ u ∈ U.filter (· ∈ A), f u := by
    rw [Finset.sum_congr rfl hav', ← Finset.smul_sum, Finset.sum_comm]
    have e1 : ∀ u ∈ U, ∑ η ∈ R, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) • f u =
        (if u ∈ A then (R.card : ℂ) else 0) • f u := fun u hu => by
      rw [← Finset.sum_smul, sum_char hψ hψ1 hA hR u (hU1 u hu)]
    rw [Finset.sum_congr rfl e1, Finset.sum_filter, mul_smul]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp

  have hper : ∀ a, ∀ d ∈ H, f (a + d) = f a := by
    intro a d hd
    simp only [hfdef, dotProduct_add, AddChar.map_add_eq_mul, hHξ d hd, mul_one, colEl_add, map_mul,
      Module.End.mul_apply, hHv d hd]
  have hind : ∑ u ∈ U.filter (· ∈ A), f u = ∑ t ∈ S, f t :=
    sum_tr_indep A H _ S (isTr_filter A A' H hHA U ⟨hU1, hU2⟩ hAA) ⟨hS1, hS2⟩ f hper
  have cU : U.card = H.relIndex A' := GlobalTheory.T.card_coset_reps_eq_relIndex _ A' H U (hHA.trans hAA) hU1 hU2
  have cS : S.card = H.relIndex A := GlobalTheory.T.card_coset_reps_eq_relIndex _ A H S hHA hS1 hS2
  have cT : T.card = A.relIndex A' := GlobalTheory.T.card_coset_reps_eq_relIndex _ A' A T hAA hT.1 hT.2
  have cmul : U.card = S.card * T.card := by
    rw [cU, cS, cT, AddSubgroup.relIndex_mul_relIndex H A A' hHA hAA]
  have hS0 : (S.card : ℂ) ≠ 0 := by
    obtain ⟨t, ht, -⟩ := hS2 0 A.zero_mem
    exact_mod_cast (Finset.card_pos.2 ⟨t, ht.1⟩).ne'
  have hT0 : (T.card : ℂ) ≠ 0 := by
    obtain ⟨t, ht, -⟩ := hT.2 0 A'.zero_mem
    exact_mod_cast (Finset.card_pos.2 ⟨t, ht.1⟩).ne'
  rw [hsum, hind, hav, smul_smul, smul_smul, cmul]
  congr 1
  push_cast
  field_simp

end

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end
end
