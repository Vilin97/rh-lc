module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreFiniteCard
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibre

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.MassFibre

theorem card_mul_relIndex {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  have h2 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2] at h1
  exact h1

theorem encard_coe_subgroup {G : Type} [Group G] (H : Subgroup G) :
    ((H : Set G).encard : ℝ≥0∞) = if Nat.card H = 0 then ⊤ else (Nat.card H : ℝ≥0∞) := by
  split_ifs with h
  · have : (H : Set G).Infinite := by
      rcases Nat.card_eq_zero.mp h with h' | h'
      · exact absurd h' (not_isEmpty_of_nonempty _)
      · exact Set.infinite_coe_iff.mp h'
    rw [Set.encard_eq_top_iff.mpr this]; rfl
  · have hf : (H : Set G).Finite := by
      have := Nat.finite_of_card_ne_zero h
      exact Set.toFinite _
    rw [← hf.cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl

theorem inv_encard_eq_relIndex_mul {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K)
    (hr : H.relIndex K ≠ 0) :
    (((H : Set G).encard : ℝ≥0∞))⁻¹ = (H.relIndex K : ℝ≥0∞) * (((K : Set G).encard : ℝ≥0∞))⁻¹ := by
  have hc := card_mul_relIndex H K hle
  rw [encard_coe_subgroup, encard_coe_subgroup]
  by_cases hK : Nat.card K = 0
  · have hH : Nat.card H = 0 := by
      rw [hK] at hc
      rcases Nat.mul_eq_zero.mp hc with h | h
      · exact h
      · exact absurd h hr
    simp [hH, hK]
  · have hH : Nat.card H ≠ 0 := by
      intro h; rw [h, zero_mul] at hc; exact hK hc.symm
    rw [if_neg hH, if_neg hK, ← hc]
    push_cast
    rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hH)) (Or.inl (by simp)), mul_comm,
      mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hr) (by simp), mul_one]

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

open MulAction

noncomputable def wt {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) : ℝ≥0∞ :=
  ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹

theorem wt_smul {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (γ : G)
    (hγ : γ ∈ Γ) (y : Y) : wt Γ (γ • y) = wt Γ y := by
  unfold wt
  congr 2
  have hset : ((Γ ⊓ MulAction.stabilizer G (γ • y) : Subgroup G) : Set G)
      = (fun h => γ * h * γ⁻¹) '' ((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G) := by
    ext x
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Set.mem_image]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨γ⁻¹ * x * γ, ⟨?_, ?_⟩, by group⟩
      · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hx1) hγ
      · rw [mul_smul, mul_smul, hx2, inv_smul_smul]
    · rintro ⟨h, ⟨hh1, hh2⟩, rfl⟩
      refine ⟨Γ.mul_mem (Γ.mul_mem hγ hh1) (Γ.inv_mem hγ), ?_⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hh2]
  rw [hset, Function.Injective.encard_image]
  intro a b hab
  simpa using hab

theorem wt_of_mem_orbit {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y]
    {y y' : Y} (h : y' ∈ MulAction.orbit Γ y) : wt Γ y' = wt Γ y := by
  obtain ⟨γ, rfl⟩ := h
  show wt Γ (γ • y) = wt Γ y
  rw [Subgroup.smul_def]
  exact wt_smul Γ γ γ.2 y

theorem wt_out_mk {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) :
    wt Γ (Quotient.out (Quotient.mk (MulAction.orbitRel Γ Y) y : MulAction.orbitRel.Quotient Γ Y)) = wt Γ y :=
  wt_of_mem_orbit Γ (Quotient.mk_out (s := MulAction.orbitRel Γ Y) y)

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

theorem fibre_sum {G : Type} [Group G] (Γ : Subgroup G) {Y Z : Type} [MulAction G Y] [MulAction G Z]
    (f : Y → Z) (S : Set Z) (n : ℕ) (hf : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hfin : ∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n)
    (hemp : ∀ z, z ∉ S → IsEmpty {y // f y = z})
    (fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z)
    (hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y))
    (O : MulAction.orbitRel.Quotient Γ Z) :
    ∑' P : {P // fbar P = O}, wt Γ (Quotient.out P.1) = (n : ℝ≥0∞) * (if Quotient.out O ∈ S then wt Γ (Quotient.out O) else 0) := by

  classical
  by_cases hz : Quotient.out O ∈ S
  swap
  · rw [if_neg hz, mul_zero]
    haveI : IsEmpty {P // fbar P = O} := by
      refine ⟨fun ⟨P, hP⟩ => ?_⟩
      have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
          = Quotient.mk (MulAction.orbitRel Γ Z) (Quotient.out O) := by
        rw [← hfbar, Quotient.out_eq, Quotient.out_eq, hP]
      obtain ⟨γ, hγ⟩ := Quotient.exact h1
      exact (hemp _ hz).false ⟨(γ⁻¹ : G) • Quotient.out P, by
        rw [hf, ← hγ]; simp [Subgroup.smul_def]⟩
    simp
  rw [if_pos hz]
  obtain ⟨z, hzO⟩ : ∃ z, Quotient.out O = z := ⟨_, rfl⟩
  rw [hzO] at hz ⊢
  have hOz : Quotient.mk (MulAction.orbitRel Γ Z) z = O := by rw [← hzO, Quotient.out_eq]
  let Δ : Subgroup G := Γ ⊓ MulAction.stabilizer G z
  have hΔ : ∀ {g : G}, g ∈ Δ ↔ g ∈ Γ ∧ g • z = z := fun {g} => by
    simp [Δ, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  let p : SubMulAction Δ Y :=
    { carrier := f ⁻¹' {z}
      smul_mem' := fun δ y hy => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        rw [Subgroup.smul_def, hf, hy]; exact (hΔ.mp δ.2).2 }
  have hmem : ∀ y : Y, y ∈ p ↔ f y = z := fun y => Iff.rfl
  let e : p ≃ {y // f y = z} := Equiv.subtypeEquivRight hmem
  haveI : Finite {y // f y = z} := (hfin z hz).1
  haveI : Finite p := Finite.of_equiv _ e.symm
  have hcard : Nat.card p = n := (Nat.card_congr e).trans (hfin z hz).2

  let φ : MulAction.orbitRel.Quotient Δ p → {P // fbar P = O} := fun Q =>
    ⟨Quotient.mk _ (Quotient.out Q : p).1, by
      rw [hfbar, (hmem _).mp (Quotient.out Q).2, hOz]⟩
  have hinj : Function.Injective φ := by
    intro Q1 Q2 h
    have h' := congrArg Subtype.val h
    obtain ⟨γ, hγ⟩ := Quotient.exact h'
    have hγΔ : (γ : G) ∈ Δ := by
      refine hΔ.mpr ⟨γ.2, ?_⟩
      have hy1 := (hmem _).mp (Quotient.out Q1).2
      have hy2 := (hmem _).mp (Quotient.out Q2).2
      calc (γ : G) • z = (γ : G) • f (Quotient.out Q2 : p).1 := by rw [hy2]
        _ = f ((γ : G) • (Quotient.out Q2 : p).1) := (hf _ _).symm
        _ = f (Quotient.out Q1 : p).1 := by rw [← hγ]; rfl
        _ = z := hy1
    rw [← Quotient.out_equiv_out]
    refine ⟨⟨γ, hγΔ⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
        = Quotient.mk (MulAction.orbitRel Γ Z) z := by
      rw [← hfbar, Quotient.out_eq, hP, hOz]
    obtain ⟨γ, hγ⟩ := Quotient.exact h1
    let y' : p := ⟨(γ⁻¹ : G) • Quotient.out P, by
      rw [hmem, hf, ← hγ]; simp [Subgroup.smul_def]⟩
    refine ⟨Quotient.mk _ y', Subtype.ext ?_⟩
    obtain ⟨δ, hδ⟩ := (Quotient.mk_out (s := MulAction.orbitRel Δ p) y')
    show Quotient.mk _ _ = P
    conv_rhs => rw [← Quotient.out_eq P]
    apply Quotient.sound
    refine ⟨⟨(δ : G) * (γ : G)⁻¹, Γ.mul_mem (hΔ.mp δ.2).1 (Γ.inv_mem γ.2)⟩, ?_⟩
    rw [← hδ]
    show ((δ : G) * (γ : G)⁻¹) • Quotient.out P = (δ : G) • ((γ⁻¹ : G) • Quotient.out P)
    rw [mul_smul]

  have hw : ∀ y : p, wt Γ (y : Y) = ((MulAction.orbit Δ y).ncard : ℝ≥0∞) * wt Γ z := by
    intro y
    have hy := (hmem _).mp y.2
    have hle : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G) ≤ Δ := by
      intro g hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg
      refine hΔ.mpr ⟨hg.1, ?_⟩
      rw [← hy, ← hf, hg.2]
    have hsub : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).subgroupOf Δ
        = MulAction.stabilizer Δ y := by
      ext δ
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
        MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨-, h⟩; exact Subtype.ext h
      · intro h; exact ⟨(hΔ.mp δ.2).1, congrArg Subtype.val h⟩
    have hri : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).relIndex Δ
        = (MulAction.orbit Δ y).ncard := by
      rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer]
    have hne : (MulAction.orbit Δ y).ncard ≠ 0 :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨y, MulAction.mem_orbit_self y⟩ |>.ne'
    unfold wt
    rw [inv_encard_eq_relIndex_mul _ _ hle (hri ▸ hne), hri]
  rw [← (Equiv.ofBijective φ ⟨hinj, hsurj⟩).tsum_eq]
  haveI : Fintype (MulAction.orbitRel.Quotient Δ p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hterm : ∀ Q : MulAction.orbitRel.Quotient Δ p,
      wt Γ (Quotient.out (Equiv.ofBijective φ ⟨hinj, hsurj⟩ Q).1)
        = ((MulAction.orbit Δ (Quotient.out Q)).ncard : ℝ≥0∞) * wt Γ z := by
    intro Q
    rw [← hw]
    exact wt_out_mk Γ _
  simp_rw [hterm, ← Finset.sum_mul]
  congr 1
  have hsum : ∑ Q : MulAction.orbitRel.Quotient Δ p, (MulAction.orbit Δ (Quotient.out Q)).ncard = n := by
    rw [← hcard, Nat.card_congr (MulAction.selfEquivSigmaOrbits Δ p), Nat.card_sigma]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Nat.card_coe_set_eq]
  rw [← hsum]
  push_cast
  rfl

theorem mass_fibre : ∀ {G : Type} [Group G] (Γ : Subgroup G) (Y Z : Type) [MulAction G Y] [MulAction G Z] (f : Y → Z) (S : Set Z) (n : ℕ), (∀ (g : G) (y : Y), f (g • y) = g • f y) → (∀ (g : G) (z : Z), z ∈ S → g • z ∈ S) → (∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n) → (∀ z, z ∉ S → IsEmpty {y // f y = z}) → (∑' o : MulAction.orbitRel.Quotient Γ Y, ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) = (n : ℝ≥0∞) * ∑' o : MulAction.orbitRel.Quotient Γ Z, if o.out ∈ S then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0 := by
  intro G _ Γ Y Z _ _ f S n hf hS hfin hemp
  let fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z :=
    Quotient.map' f (fun a b h => by
      obtain ⟨γ, hγ⟩ := h
      refine ⟨γ, ?_⟩
      show (γ : G) • f b = f a
      rw [← hf, ← hγ]; rfl)
  have hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y) := fun y => rfl
  have key := fibre_sum Γ f S n hf hfin hemp fbar hfbar
  change ∑' o : MulAction.orbitRel.Quotient Γ Y, wt Γ (Quotient.out o) = _
  rw [← (Equiv.sigmaFiberEquiv fbar).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun O => ?_)
  exact key O

end GlobalTheory.MassFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibreStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.orbit_mass_equivariant_constant_fibre : ∀ {G : Type} [Group G] (Γ : Subgroup G) (Y Z : Type) [MulAction G Y] [MulAction G Z] (f : Y → Z) (S : Set Z) (n : ℕ), (∀ (g : G) (y : Y), f (g • y) = g • f y) → (∀ (g : G) (z : Z), z ∈ S → g • z ∈ S) → (∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n) → (∀ z, z ∉ S → IsEmpty {y // f y = z}) → (∑' o : MulAction.orbitRel.Quotient Γ Y, ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) = (n : ℝ≥0∞) * ∑' o : MulAction.orbitRel.Quotient Γ Z, if o.out ∈ S then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0 := by
  first | exact @GlobalTheory.MassFibre.mass_fibre | exact GlobalTheory.MassFibre.mass_fibre | (intros; apply GlobalTheory.MassFibre.mass_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolume

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem coset_fibre_card {G : Type} [Group G] (D H : Subgroup G) (h : D ≤ H) (hDH : D.relIndex H ≠ 0)
    (z : G ⧸ H) : Finite {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ∧
      Nat.card {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} = D.relIndex H := by
  apply GlobalTheory.FibreEquivalence.fibre_finite_card <;> assumption

theorem mass_orbit_eq : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V₀ : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V₀ * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0
  let M : Subgroup G → ℝ≥0∞ := fun U => ∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ U),
    ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹
  have hq : ∀ (D H : Subgroup G) (h : D ≤ H), D.relIndex H ≠ 0 → M D = (D.relIndex H : ℝ≥0∞) * M H := by
    intro D H h hDH
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ D) (G ⧸ H) (Subgroup.quotientMapOfLE h) Set.univ (D.relIndex H) ?_
      (fun _ _ _ => trivial) (fun z _ => coset_fibre_card D H h hDH z) (fun z hz => absurd trivial hz)
    · simp only [Set.mem_univ, ite_true] at e
      exact e
    · intro g y
      induction y using QuotientGroup.induction_on with
      | H a => rfl
  refine ⟨M K0, fun X _ x h1 h2 => ?_⟩
  have hX : (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) =
      M (MulAction.stabilizer G x) := by
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ MulAction.stabilizer G x) X (MulAction.ofQuotientStabilizer G x)
      (MulAction.orbit G x) 1 (fun g y => MulAction.ofQuotientStabilizer_smul G x g y)
      (fun g z hz => by obtain ⟨a, rfl⟩ := hz; exact ⟨g * a, mul_smul g a x⟩) ?_ ?_
    · rw [Nat.cast_one, one_mul] at e
      exact e.symm
    · intro z hz
      have hs : Subsingleton {y // MulAction.ofQuotientStabilizer G x y = z} :=
        ⟨fun a b => Subtype.ext (MulAction.injective_ofQuotientStabilizer G x (a.2.trans b.2.symm))⟩
      obtain ⟨a, rfl⟩ := hz
      have hn : Nonempty {y // MulAction.ofQuotientStabilizer G x y = a • x} :=
        ⟨⟨(a : G ⧸ MulAction.stabilizer G x), MulAction.ofQuotientStabilizer_mk G x a⟩⟩
      exact ⟨inferInstance, Nat.card_unique⟩
    · intro z hz
      refine ⟨fun y => hz ?_⟩
      rw [← y.2]
      induction y.1 using QuotientGroup.induction_on with
      | H a => exact ⟨a, (MulAction.ofQuotientStabilizer_mk G x a).symm⟩
  rw [hX]
  set U := MulAction.stabilizer G x
  have ha := hq (U ⊓ K0) U inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact h1)
  have hb := hq (U ⊓ K0) K0 inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact h2)
  rw [Subgroup.inf_relIndex_left] at ha
  rw [Subgroup.inf_relIndex_right] at hb
  rw [ha] at hb
  have hr : ENNReal.ofReal (invVol K0 U) = (U.relIndex K0 : ℝ≥0∞) / (K0.relIndex U : ℝ≥0∞) := by
    rw [invVol, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have hA : (K0.relIndex U : ℝ≥0∞) ≠ 0 := by exact_mod_cast h1
  have hA' : (K0.relIndex U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hr, ← mul_div_assoc, ENNReal.eq_div_iff hA hA', mul_comm (M K0), ← hb]

end GlobalTheory.HL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolumeStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V0 : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V0 * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  first | exact @GlobalTheory.HL.mass_orbit_eq | exact GlobalTheory.HL.mass_orbit_eq | (intros; apply GlobalTheory.HL.mass_orbit_eq <;> assumption)
end
end
