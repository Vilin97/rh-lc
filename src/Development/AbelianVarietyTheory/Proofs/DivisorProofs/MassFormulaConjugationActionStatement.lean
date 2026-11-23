module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOverConjPairsEqOrbitSum
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
public import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClass

section

@[expose] public section

open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_out_mk_eq_smul {H α : Type} [Group H] [MulAction H α] (a : α) :
    ∃ g : H, Quotient.out (Quotient.mk (MulAction.orbitRel H α) a :
      MulAction.orbitRel.Quotient H α) = g • a := by
  have h := Quotient.mk_out (s := MulAction.orbitRel H α) a
  change MulAction.orbitRel H α _ _ at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

theorem finsum_pairOrbit_fibre (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G)
    (Φ : Γ → X → ℂ)
    (hΦ : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) (γ₀ : Γ) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  set C : Subgroup G := Γ ⊓ Subgroup.centralizer {(γ₀ : G)} with hC
  have memC : ∀ δ : Γ, δ * γ₀ = γ₀ * δ → (δ : G) ∈ C := by
    intro δ h
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨δ.2, ?_⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have := congrArg (fun z : Γ => (z : G)) h
    simpa using this.symm
  have commC : ∀ c : C, (⟨c, c.2.1⟩ : Γ) * γ₀ = γ₀ * ⟨c, c.2.1⟩ := by
    intro c
    have h2 := (Subgroup.mem_inf.mp c.2).2
    rw [Subgroup.mem_centralizer_iff] at h2
    have h := h2 γ₀ (Set.mem_singleton _)
    ext
    simp [h]
  let f : MulAction.orbitRel.Quotient C X →
      {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀} :=
    fun b => ⟨Quotient.mk _ ⟨γ₀, Quotient.out b⟩, by
      obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
      rw [hδ, smul_elt, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨δ⁻¹, by group⟩⟩
  have inj : Function.Injective f := by
    intro b b' hbb
    have h1 := congrArg Subtype.val hbb
    simp only [f] at h1
    have h2 := Quotient.exact h1
    change MulAction.orbitRel Γ _ _ _ at h2
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h2
    obtain ⟨δ, hδ⟩ := h2
    have he := congrArg ConjPair.elt hδ
    have hp := congrArg ConjPair.pt hδ
    simp only [smul_elt, smul_pt] at he hp
    have hcomm : δ * γ₀ = γ₀ * δ := by
      calc δ * γ₀ = δ * γ₀ * δ⁻¹ * δ := by group
        _ = γ₀ * δ := by rw [he]
    rw [← Quotient.out_eq b, ← Quotient.out_eq b']
    apply Quotient.sound
    change MulAction.orbitRel C X _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨δ, memC δ hcomm⟩, hp⟩
  have surj : Function.Surjective f := by
    rintro ⟨O, hO⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hO
    obtain ⟨δ, hδ⟩ := hO
    obtain ⟨c, hc⟩ := exists_out_mk_eq_smul (H := C) (δ • (Quotient.out O).pt)
    refine ⟨Quotient.mk _ (δ • (Quotient.out O).pt), ?_⟩
    apply Subtype.ext
    simp only [f]
    conv_rhs => rw [← Quotient.out_eq O]
    apply Quotient.sound
    change MulAction.orbitRel Γ _ _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨(⟨c, c.2.1⟩ : Γ) * δ, ?_⟩
    rw [hc, mul_smul]
    ext
    · simp only [smul_elt]
      rw [hδ, commC c]
      group
    · simp only [smul_pt]
      rfl
  have term : ∀ b : MulAction.orbitRel.Quotient C X,
      (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out (f b).1)) : ℂ)) *
          Φ (Quotient.out (f b).1).elt (Quotient.out (f b).1).pt =
        (1 / (Nat.card (MulAction.stabilizer C (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
    intro b
    obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
    have hfb : (f b).1 = Quotient.mk _ (ConjPair.mk γ₀ (Quotient.out b)) := rfl
    rw [hfb, hδ, smul_elt, smul_pt]
    have hcard1 : Nat.card (MulAction.stabilizer Γ (δ • ConjPair.mk γ₀ (Quotient.out b))) =
        Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b))) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer rfl).toEquiv.symm
    have h_to : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        ((s : Γ) : G) ∈ C := fun s =>
      memC s.1 ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).1
    have h_to' : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        (⟨((s : Γ) : G), h_to s⟩ : C) ∈ MulAction.stabilizer C (Quotient.out b) := by
      intro s
      rw [MulAction.mem_stabilizer_iff]
      exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).2
    have h_inv : ∀ t : MulAction.stabilizer C (Quotient.out b),
        (⟨((t : C) : G), (t : C).2.1⟩ : Γ) ∈
          MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X) := by
      intro t
      rw [GlobalTheory.MassConj.mem_stabilizer_iff]
      exact ⟨commC t.1, MulAction.mem_stabilizer_iff.mp t.2⟩
    have hcard2 : Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X)) =
        Nat.card (MulAction.stabilizer C (Quotient.out b)) :=
      Nat.card_congr
        { toFun := fun s => ⟨⟨((s : Γ) : G), h_to s⟩, h_to' s⟩
          invFun := fun t => ⟨⟨((t : C) : G), (t : C).2.1⟩, h_inv t⟩
          left_inv := fun s => rfl
          right_inv := fun t => rfl }
    have hphi : Φ (δ * γ₀ * δ⁻¹) (δ • Quotient.out b) = Φ γ₀ (Quotient.out b) :=
      hΦ δ γ₀ (Quotient.out b)
    rw [hcard1, hcard2, hphi]
  refine (finsum_comp_equiv (Equiv.ofBijective f ⟨inj, surj⟩)).symm.trans ?_
  exact finsum_congr term

end GlobalTheory.MassConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClassStatement

section

@[expose] public section

open scoped Classical

theorem _root_.GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    ∀ γ₀ : Γ, ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  first | (exact @GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (exact GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (intros; apply GlobalTheory.MassConj.finsum_pairOrbit_fibre  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassFormulaConjugationAction

section

@[expose] public section

open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_smul_eq_out' {T α : Type} [Group T] [MulAction T α] (p : α) :
    ∃ t : T, t • p = Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α) := by
  have h : (Quotient.mk'' (Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α)) :
      MulAction.orbitRel.Quotient T α) = Quotient.mk'' p := Quotient.out_eq' _
  exact MulAction.orbitRel_apply.1 (Quotient.eq''.1 h)

theorem finite_support_pairs : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite := by
  intro H _ X _ f hinv hfo hsupp
  refine (Set.finite_iUnion fun a : MulAction.orbitRel.Quotient H X =>
    (hsupp (Quotient.out a)).image fun γ => (Quotient.mk'' (ConjPair.mk γ (Quotient.out a)) :
      MulAction.orbitRel.Quotient H (ConjPair H X))).subset ?_
  intro O hO
  have hO' : f (Quotient.out O).elt (Quotient.out O).pt ≠ 0 := hO
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := H) (Quotient.out O).pt
  refine Set.mem_iUnion.2 ⟨Quotient.mk'' (Quotient.out O).pt, δ * (Quotient.out O).elt * δ⁻¹, ?_, ?_⟩
  · show f _ _ ≠ 0
    rw [← hδ, hinv]; exact hO'
  · have e : ConjPair.mk (δ * (Quotient.out O).elt * δ⁻¹)
        (Quotient.out (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) =
        δ • Quotient.out O := by
      rw [← hδ]; rfl
    show (Quotient.mk'' (ConjPair.mk _ _) : MulAction.orbitRel.Quotient H (ConjPair H X)) = O
    rw [e]
    exact (Quotient.sound' (MulAction.mem_orbit _ δ)).trans (Quotient.out_eq' O)

theorem finite_support_weighted {H X : Type} [Group H] [MulAction H X] (f : H → X → ℂ)
    (hfin : {O : MulAction.orbitRel.Quotient H (ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite) :
    (Function.support fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
        f (Quotient.out O).elt (Quotient.out O).pt).Finite := by
  refine hfin.subset fun O hO => ?_
  exact right_ne_zero_of_mul hO

theorem mass_pt_side : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) → (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ a : MulAction.orbitRel.Quotient H X,
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * ∑ᶠ γ : H, f γ (Quotient.out a) =
      ∑ᶠ O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
          f (Quotient.out O).elt (Quotient.out O).pt := by
  intro H _ X _ f hinv hfo hstab hsupp hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) _
    (finite_support_weighted f hfin)]
  refine finsum_congr fun a => ?_
  have h := GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum H X f hinv hstab hsupp (Quotient.out a)
  rw [Quotient.out_eq'] at h
  exact h.symm

theorem mass_class_side : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) |
      Φ (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X),
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O)) : ℂ)) *
          Φ (Quotient.out O).elt (Quotient.out O).pt =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hstab hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) => ConjClasses.mk (Quotient.out O).elt) _
    (finite_support_weighted Φ hfin)]
  refine finsum_congr fun c => ?_
  have h := GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass G X Γ Φ hinv (Quotient.out c)
  have e : ConjClasses.mk (Quotient.out c) = c := Quotient.out_eq c
  rw [e] at h
  exact h

theorem mass_formula_conj : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    Finite (MulAction.orbitRel.Quotient Γ X) → (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    (∀ x : X, (Function.support fun γ : Γ => Φ γ x).Finite) →
    {c : ConjClasses Γ | ∃ x : X, Φ (Quotient.out c) x ≠ 0}.Finite ∧
    ∑ᶠ a : MulAction.orbitRel.Quotient Γ X,
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out a)) : ℂ)) * ∑ᶠ γ : Γ, Φ γ (Quotient.out a) =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hfo hstab hsupp
  have hinv' : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) (δ • x) = Φ γ x := fun δ γ x => hinv δ γ x
  have hfin := finite_support_pairs Γ X Φ hinv' hfo hsupp
  refine ⟨?_, mass_pt_side Γ X Φ hinv' hfo hstab hsupp hfin |>.trans (mass_class_side G X Γ Φ hinv hstab hfin)⟩
  refine (hfin.image (fun O => ConjClasses.mk (Quotient.out O).elt)).subset ?_
  rintro c ⟨x, hx⟩
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := Γ) (ConjPair.mk (Quotient.out c) x)
  refine ⟨Quotient.mk'' (ConjPair.mk (Quotient.out c) x), ?_, ?_⟩
  · show Φ _ _ ≠ 0
    rw [← hδ, smul_elt, smul_pt, hinv']
    exact hx
  · show ConjClasses.mk _ = c
    rw [← hδ, smul_elt]
    calc ConjClasses.mk (δ * Quotient.out c * δ⁻¹) = ConjClasses.mk (Quotient.out c) :=
          ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨δ, rfl⟩).symm
      _ = c := Quotient.out_eq c

end GlobalTheory.MassConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassFormulaConjugationActionStatement

section

@[expose] public section

open scoped Classical

theorem _root_.GlobalTheory.T.massFormula_conjugation_action : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    Finite (MulAction.orbitRel.Quotient Γ X) → (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    (∀ x : X, (Function.support fun γ : Γ => Φ γ x).Finite) →
    {c : ConjClasses Γ | ∃ x : X, Φ (Quotient.out c) x ≠ 0}.Finite ∧
    ∑ᶠ a : MulAction.orbitRel.Quotient Γ X,
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out a)) : ℂ)) * ∑ᶠ γ : Γ, Φ γ (Quotient.out a) =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  first | exact @GlobalTheory.MassConj.mass_formula_conj | exact GlobalTheory.MassConj.mass_formula_conj | (intros; apply GlobalTheory.MassConj.mass_formula_conj <;> assumption)
end
end
