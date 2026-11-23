module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Quotient
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliserStatement
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountFib

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.CC.Fib

open MulAction

variable {G : Type*} [Group G]

def Gam (Γ K : Subgroup G) (g : G) : Subgroup G :=
  Γ ⊓ K.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_Gam {Γ K : Subgroup G} {g x : G} : x ∈ Gam Γ K g ↔ x ∈ Γ ∧ g⁻¹ * x * g ∈ K := by
  simp [Gam, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem Gam_eq_map (Γ K : Subgroup G) (g : G) :
    Gam Γ K g = Γ ⊓ K.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_Gam, Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hx, hk⟩
    refine ⟨hx, _, hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨hx, k, hk, rfl⟩
    refine ⟨hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert hk using 1
    group

def GamEquivSet (Γ K : Subgroup G) (g : G) : Gam Γ K g ≃ {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} where
  toFun x := ⟨⟨x.1, (mem_Gam.1 x.2).1⟩, (mem_Gam.1 x.2).2⟩
  invFun y := ⟨y.1.1, mem_Gam.2 ⟨y.1.2, y.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def GamCongr {Γ U : Subgroup G} {x x' h u : G} (hh : h ∈ Γ) (hu : u ∈ U) (e : x' = h * x * u) :
    Gam Γ U x ≃* Gam Γ U x' where
  toFun y := ⟨h * y * h⁻¹, mem_Gam.2 ⟨Γ.mul_mem (Γ.mul_mem hh (mem_Gam.1 y.2).1) (Γ.inv_mem hh), by
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) (mem_Gam.1 y.2).2) hu
    rw [e]; convert this using 1; group⟩⟩
  invFun y := ⟨h⁻¹ * y * h, mem_Gam.2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hh) (mem_Gam.1 y.2).1) hh, by
    have := U.mul_mem (U.mul_mem hu (mem_Gam.1 y.2).2) (U.inv_mem hu)
    subst e; convert this using 1; group⟩⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' y z := by ext; simp [mul_assoc]

def toK (Γ K : Subgroup G) (g : G) : Gam Γ K g →* K where
  toFun x := ⟨g⁻¹ * x * g, (mem_Gam.1 x.2).2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] theorem toK_coe (Γ K : Subgroup G) (g : G) (x : Gam Γ K g) : (toK Γ K g x : G) = g⁻¹ * x * g := rfl

instance actK (Γ K U : Subgroup G) (g : G) : MulAction (Gam Γ K g) (K ⧸ U.subgroupOf K) :=
  MulAction.compHom _ (toK Γ K g)

theorem smul_mk (Γ K U : Subgroup G) (g : G) (x : Gam Γ K g) (k : K) :
    x • (k : K ⧸ U.subgroupOf K) = ((toK Γ K g x * k : K) : K ⧸ U.subgroupOf K) := rfl

theorem mk_eq_iff {K U : Subgroup G} {k k' : K} :
    (k : K ⧸ U.subgroupOf K) = (k' : K ⧸ U.subgroupOf K) ↔ (k : G)⁻¹ * k' ∈ U := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

def stabEquiv {Γ K U : Subgroup G} (hUK : U ≤ K) (g : G) (k : K) :
    stabilizer (Gam Γ K g) (k : K ⧸ U.subgroupOf K) ≃* Gam Γ U (g * k) where
  toFun x := ⟨x.1.1, mem_Gam.2 ⟨(mem_Gam.1 x.1.2).1, by
    have h := x.2
    rw [mem_stabilizer_iff, smul_mk, eq_comm, mk_eq_iff] at h
    simpa [mul_assoc] using h⟩⟩
  invFun y := ⟨⟨y.1, mem_Gam.2 ⟨(mem_Gam.1 y.2).1, by
      have h := K.mul_mem (K.mul_mem k.2 (hUK (mem_Gam.1 y.2).2)) (K.inv_mem k.2)
      simpa [mul_assoc] using h⟩⟩, by
    rw [mem_stabilizer_iff, smul_mk, eq_comm, mk_eq_iff]
    simpa [mul_assoc] using (mem_Gam.1 y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def toCls (Γ K U : Subgroup G) (g : G) : K ⧸ U.subgroupOf K → DoubleCoset.Quotient (Γ : Set G) U :=
  Quotient.lift (fun k : K => DoubleCoset.mk Γ U (g * k)) (by
    intro a b h
    have h' : (a : G)⁻¹ * b ∈ U := by
      have := QuotientGroup.leftRel_apply.1 h
      simpa [Subgroup.mem_subgroupOf] using this
    exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨1, Γ.one_mem, _, h', by simp [mul_assoc]⟩)

@[simp] theorem toCls_mk (Γ K U : Subgroup G) (g : G) (k : K) :
    toCls Γ K U g (k : K ⧸ U.subgroupOf K) = DoubleCoset.mk Γ U (g * k) := rfl

theorem toCls_smul (Γ K U : Subgroup G) (g : G) (x : Gam Γ K g) (y : K ⧸ U.subgroupOf K) :
    toCls Γ K U g (x • y) = toCls Γ K U g y := by
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [smul_mk, toCls_mk, toCls_mk]
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(x : G)⁻¹, Γ.inv_mem (mem_Gam.1 x.2).1, 1, U.one_mem, ?_⟩
    simp only [Subgroup.coe_mul, toK_coe]
    group

def orbToCls (Γ K U : Subgroup G) (g : G) :
    orbitRel.Quotient (Gam Γ K g) (K ⧸ U.subgroupOf K) → DoubleCoset.Quotient (Γ : Set G) U :=
  Quotient.lift (toCls Γ K U g) (by
    rintro a b ⟨x, rfl⟩
    exact toCls_smul Γ K U g x b)

@[simp] theorem orbToCls_mk (Γ K U : Subgroup G) (g : G) (y : K ⧸ U.subgroupOf K) :
    orbToCls Γ K U g (Quotient.mk'' y) = toCls Γ K U g y := rfl

def total (Γ K U : Subgroup G) (rep : DoubleCoset.Quotient (Γ : Set G) K → G) :
    (Σ c : DoubleCoset.Quotient (Γ : Set G) K, orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K)) →
      DoubleCoset.Quotient (Γ : Set G) U :=
  fun p => orbToCls Γ K U (rep p.1) p.2

theorem total_surjective (Γ K U : Subgroup G) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) : Function.Surjective (total Γ K U rep) := by
  intro q
  obtain ⟨h, hh, k, hk, hx⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 (hrep (DoubleCoset.mk Γ K (Quotient.out q)))
  refine ⟨⟨DoubleCoset.mk Γ K (Quotient.out q), Quotient.mk'' ((⟨k, hk⟩ : K) : K ⧸ U.subgroupOf K)⟩, ?_⟩
  show orbToCls Γ K U _ (Quotient.mk'' _) = q
  rw [orbToCls_mk, toCls_mk]
  conv_rhs => rw [← DoubleCoset.out_eq' (H := Γ) (K := U) q]
  refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨h, hh, 1, U.one_mem, ?_⟩
  rw [mul_one, ← mul_assoc]
  exact hx

theorem total_injective {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) : Function.Injective (total Γ K U rep) := by
  rintro ⟨c, o⟩ ⟨c', o'⟩ heq
  induction o using Quotient.inductionOn' with
  | h y =>
  induction o' using Quotient.inductionOn' with
  | h y' =>
  induction y using QuotientGroup.induction_on with
  | H k =>
  induction y' using QuotientGroup.induction_on with
  | H k' =>
  have heq' : DoubleCoset.mk Γ U (rep c * k) = DoubleCoset.mk Γ U (rep c' * k') := heq
  obtain ⟨h, hh, u, hu, he⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1 heq'
  have hcc : c = c' := by
    rw [← hrep c, ← hrep c']
    refine (@DoubleCoset.eq _ _ Γ K _ _).2 ⟨h, hh, (k : G) * u * (k' : G)⁻¹,
      K.mul_mem (K.mul_mem k.2 (hUK hu)) (K.inv_mem k'.2), ?_⟩
    rw [eq_mul_inv_of_mul_eq he]
    group
  subst hcc
  have e1 : h = rep c * k' * u⁻¹ * (k : G)⁻¹ * (rep c)⁻¹ := by
    rw [he]
    group
  have hx : h⁻¹ ∈ Gam Γ K (rep c) := by
    refine mem_Gam.2 ⟨Γ.inv_mem hh, ?_⟩
    have : (rep c)⁻¹ * h⁻¹ * rep c = (k : G) * u * (k' : G)⁻¹ := by
      rw [e1]
      group
    rw [this]
    exact K.mul_mem (K.mul_mem k.2 (hUK hu)) (K.inv_mem k'.2)
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  refine Quotient.sound ⟨⟨h⁻¹, hx⟩, ?_⟩
  show (⟨h⁻¹, hx⟩ : Gam Γ K (rep c)) • ((k' : K) : K ⧸ U.subgroupOf K) = ((k : K) : K ⧸ U.subgroupOf K)
  rw [smul_mk, mk_eq_iff]
  simp only [Subgroup.coe_mul, toK_coe]
  rw [e1]
  convert U.inv_mem hu using 1
  group

def fibRep {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) :
    DoubleCoset.Quotient (Γ : Set G) U ≃
      Σ c : DoubleCoset.Quotient (Γ : Set G) K, orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K) :=
  (Equiv.ofBijective (total Γ K U rep) ⟨total_injective hUK rep hrep, total_surjective Γ K U rep hrep⟩).symm

theorem fibRep_symm_mk {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) (c : DoubleCoset.Quotient (Γ : Set G) K) (k : K) :
    (fibRep hUK rep hrep).symm ⟨c, Quotient.mk'' (k : K ⧸ U.subgroupOf K)⟩ = DoubleCoset.mk Γ U (rep c * k) := rfl

def fib {Γ K U : Subgroup G} (hUK : U ≤ K) :
    DoubleCoset.Quotient (Γ : Set G) U ≃
      Σ c : DoubleCoset.Quotient (Γ : Set G) K,
        orbitRel.Quotient (Gam Γ K (Quotient.out c)) (K ⧸ U.subgroupOf K) :=
  fibRep hUK Quotient.out (DoubleCoset.out_eq' (H := Γ) (K := K))


end Formalism.MainNotions.Gaps.CC.Fib
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.BCT.OrbLev
open Formalism.MainNotions.Gaps.CC.Fib MulAction Function

variable {G : Type} [Group G]

theorem twCent_left (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (y : G) :
    (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * δ * θ y := by
  have h : t * δ = δ * θ t := ht
  have h2 : t⁻¹ * δ * θ t = δ := by rw [mul_assoc, ← h]; group
  calc (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * (t⁻¹ * δ * θ t) * θ y := by rw [map_mul]; group
    _ = y⁻¹ * δ * θ y := by rw [h2]

theorem Gam_mul (Γ U : Subgroup G) {γ z u : G} (hγ : γ ∈ Γ) (hu : u ∈ U) :
    Gam Γ U (γ * z * u) = (Gam Γ U z).map (MulAut.conj γ).toMonoidHom := by
  ext w
  simp only [Subgroup.mem_map, mem_Gam, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨γ⁻¹ * w * γ, ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) h1) hγ, ?_⟩, by group⟩
    have := U.mul_mem (U.mul_mem hu h2) (U.inv_mem hu)
    convert this using 1; group
  · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem hγ h1) (Γ.inv_mem hγ), ?_⟩
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) h2) hu
    convert this using 1; group

theorem Gam_eq_stab {Γ K U : Subgroup G} (hUK : U ≤ K) (x : G) (k : K) :
    Gam Γ U (x * k) = (stabilizer (Gam Γ K x) (k : K ⧸ U.subgroupOf K)).map (Gam Γ K x).subtype := by
  ext w
  constructor
  · intro hw
    let s := (stabEquiv hUK x k).symm ⟨w, hw⟩
    exact ⟨s.1, s.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (stabEquiv hUK x k ⟨a, ha⟩).2

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem conj_mem_cpt (T : Subgroup G) {γ : G} (hγ : γ ∈ T) {t : G}
    (ht : t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}) :
    (MulAut.conj γ).toMonoidHom t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  obtain ⟨h1, h2⟩ := ht
  let h : G ≃ₜ G := (Homeomorph.mulRight γ⁻¹).trans (Homeomorph.mulLeft γ)
  have hf : ⇑h = ⇑(MulAut.conj γ).toMonoidHom := by
    funext z; simp [h, MulAut.conj_apply, mul_assoc]
  refine ⟨by simpa [MulAut.conj_apply] using T.mul_mem (T.mul_mem hγ h1) (T.inv_mem hγ), ?_⟩
  rw [← MonoidHom.map_zpowers, Subgroup.coe_map, ← hf, ← h.image_closure]
  exact h2.image h.continuous

theorem cptPart_map_conj (T : Subgroup G) {γ : G} (hγ : γ ∈ T) :
    (cptPart T).map (MulAut.conj γ).toMonoidHom = cptPart T := by
  apply le_antisymm
  · rw [cptPart, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_cpt T hγ ht
  · rw [cptPart, Subgroup.closure_le]
    intro t ht
    refine ⟨(MulAut.conj γ⁻¹).toMonoidHom t, Subgroup.subset_closure (conj_mem_cpt T (T.inv_mem hγ) ht), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem finsum_sigma_of_finite {ι : Type} {β : ι → Type} [∀ i, Finite (β i)] (h : (Σ i, β i) → ℂ)
    (hh : (support h).Finite) : ∑ᶠ p, h p = ∑ᶠ i, ∑ᶠ b, h ⟨i, b⟩ := by
  letI : ∀ i, Fintype (β i) := fun i => Fintype.ofFinite _
  set I := hh.toFinset.image Sigma.fst
  have h1 : support h ⊆ ((I.sigma fun _ => Finset.univ : Finset (Σ i, β i)) : Set _) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, and_true, I, Finset.mem_image]
    exact ⟨p, hh.mem_toFinset.2 hp, rfl⟩
  have h2 : (support fun i => ∑ᶠ b, h ⟨i, b⟩) ⊆ (I : Set ι) := by
    intro i hi
    obtain ⟨b, hb⟩ : ∃ b, h ⟨i, b⟩ ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi (finsum_eq_zero_of_forall_eq_zero hc)
    simp only [Finset.mem_coe, I, Finset.mem_image]
    exact ⟨⟨i, b⟩, hh.mem_toFinset.2 hb, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem finsum_orbits {H X : Type} [Group H] [MulAction H X] [Finite X] (φ : X → ℂ)
    (hφ : ∀ (h : H) y, φ (h • y) = φ y) :
    ∑ᶠ y, φ y = ∑ᶠ ω : orbitRel.Quotient H X, ((orbit H ω.out).ncard : ℂ) * φ ω.out := by
  letI : Fintype X := Fintype.ofFinite X
  haveI : Finite (orbitRel.Quotient H X) := Quotient.finite _
  letI : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise Finset.univ (fun y => (Quotient.mk'' y : orbitRel.Quotient H X)) φ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hmem : ∀ y, (Quotient.mk'' y : orbitRel.Quotient H X) = ω ↔ y ∈ orbit H ω.out := by
    intro y
    conv_lhs => rw [← Quotient.out_eq' ω]
    rw [Quotient.eq'']
    exact orbitRel_apply
  have hc : ∀ y ∈ Finset.univ.filter (fun y => (Quotient.mk'' y : orbitRel.Quotient H X) = ω), φ y = φ ω.out := by
    intro y hy
    obtain ⟨h, rfl⟩ := (hmem y).1 (Finset.mem_filter.1 hy).2
    exact hφ h _
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp [hmem]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem avg_const' {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H u ⊤ (fun k _ => show ∀ x, u (x * k) = u x from fun x => by rw [hu, hu]) (by simp)]
  simp only [hu, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  exact finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx)

theorem twOrb_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  intro G _ _ _ θ K _hKo hKc _hθK K' hL δ f hf hT hfin
  obtain ⟨hK'o, hK'K, hθK'⟩ := hL
  set T := twCent θ δ with hTdef
  set C := cptPart T with hCdef
  let F : G → ℂ := fun y => f (y⁻¹ * δ * θ y)
  have FT : ∀ t ∈ T, ∀ y, F (t * y) = F y := fun t ht y => by simp only [F, twCent_left θ δ ht y]
  have FK : ∀ y, ∀ k ∈ K', F (y * k) = F y := by
    intro y k hk
    simp only [F]
    have e : (y * k)⁻¹ * δ * θ (y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [map_mul]; group
    rw [e, (hf.2 _ (hθK' k hk) _).2, (hf.2 _ (K'.inv_mem hk) _).1]
  let g : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ := fun q =>
    (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * F (Quotient.out q)
  have hsecond : twOrb θ K' δ f = ∑ᶠ q, g q := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 1
    exact avg_const' _ _ fun k => FK _ k k.2
  refine ⟨?_, hsecond⟩
  rw [hsecond]
  set S := K'.subgroupOf K with hSdef
  have hn : K'.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
    have ho : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
      rw [Subgroup.coe_subgroupOf]; exact hK'o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  haveI : S.FiniteIndex := ⟨hn⟩
  haveI : Finite (K ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  have avgK : ∀ x : G, avg (fun k : K => F (x * k)) = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ y : K ⧸ S, F (x * (Quotient.out y : K)) := by
    intro x
    refine GlobalTheory.T.avg_eq_of_le_rightStabiliser K _ S (fun k hk => show ∀ z : K, F (x * ((z * k : K) : G)) = F (x * z) from fun z => ?_) hn
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact FK _ _ (Subgroup.mem_subgroupOf.1 hk)
  let e := fib (Γ := T) (K := K) hK'K
  haveI hfo : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G), Finite (orbitRel.Quotient (Gam T K (Quotient.out c)) (K ⧸ S)) :=
    fun c => Quotient.finite _
  have hc : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G),
      (((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
        ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K)) = ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
    intro c
    have hwK : T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom = Gam T K (Quotient.out c) :=
      (Gam_eq_map T K _).symm
    rw [hwK]
    have hφ : ∀ (h : Gam T K (Quotient.out c)) (y : K ⧸ S),
        F (Quotient.out c * (Quotient.out (h • y) : K)) = F (Quotient.out c * (Quotient.out y : K)) := by
      intro h y
      have e1 : ((Quotient.out (h • y) : K) : K ⧸ S) =
          ((toK T K (Quotient.out c) h * Quotient.out y : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      have hu := mk_eq_iff.1 e1.symm
      have e2 : Quotient.out c * ((Quotient.out (h • y) : K) : G) = (h : G) * (Quotient.out c * (Quotient.out y : K)) *
          (((toK T K (Quotient.out c) h * Quotient.out y : K) : G)⁻¹ * (Quotient.out (h • y) : K)) := by
        rw [Subgroup.coe_mul, toK_coe]; group
      rw [e2, FK _ _ hu, FT _ (mem_Gam.1 h.2).1]
    rw [finsum_orbits (fun y : K ⧸ S => F (Quotient.out c * (Quotient.out y : K))) hφ, mul_finsum]
    refine finsum_congr fun ω => ?_
    have hq : e.symm ⟨c, ω⟩ = DoubleCoset.mk T K' (Quotient.out c * (Quotient.out ω.out : K)) := by
      have : ω = Quotient.mk'' ((Quotient.out ω.out : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq', Quotient.out_eq']
      have h := fibRep_symm_mk hK'K Quotient.out (DoubleCoset.out_eq' (H := T) (K := K)) c (Quotient.out ω.out)
      rw [← this] at h
      exact h
    obtain ⟨γ, hγ, u, hu, hout⟩ := (@DoubleCoset.eq _ _ T K' (Quotient.out c * (Quotient.out ω.out : K))
      (Quotient.out (e.symm ⟨c, ω⟩))).1 (by rw [DoubleCoset.out_eq', hq])
    have hF : F (Quotient.out (e.symm ⟨c, ω⟩)) = F (Quotient.out c * (Quotient.out ω.out : K)) := by
      rw [hout, FK _ _ hu, FT _ hγ]
    have hCc : C.map (MulAut.conj γ).toMonoidHom = C := cptPart_map_conj T hγ
    have h1 := Subgroup.relIndex_map_map_of_injective (Gam T K' (Quotient.out c * (Quotient.out ω.out : K))) C
      (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).injective
    rw [hCc] at h1
    have h2 : ((stabilizer (Gam T K (Quotient.out c)) ω.out).map (Gam T K (Quotient.out c)).subtype).subgroupOf
        (Gam T K (Quotient.out c)) = stabilizer (Gam T K (Quotient.out c)) ω.out :=
      Subgroup.comap_map_eq_self_of_injective (Gam T K (Quotient.out c)).subtype_injective _
    have hHC : Gam T K (Quotient.out c) ≤ C := by rw [← hwK]; exact (hT _).1
    have hw : (T ⊓ K'.map (MulAut.conj (Quotient.out (e.symm ⟨c, ω⟩))).toMonoidHom).relIndex C =
        (orbit (Gam T K (Quotient.out c)) ω.out).ncard * (Gam T K (Quotient.out c)).relIndex C := by
      rw [← Gam_eq_map, hout, Gam_mul T K' hγ hu, h1, Gam_eq_stab hK'K, QuotientGroup.out_eq',
        ← Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_subtype_le _) hHC, Subgroup.relIndex, h2,
        index_stabilizer]
    simp only [g]
    rw [hw, hF]
    push_cast
    ring
  have hsupp : (support fun p => g (e.symm p)).Finite := by
    refine (hfin.preimage e.symm.injective.injOn).subset ?_
    intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro h0
    exact hp (by simp only [g]; rw [show F (Quotient.out (e.symm p)) = 0 from h0, mul_zero])
  calc twOrb θ K δ f
      = ∑ᶠ c : DoubleCoset.Quotient (T : Set G) (K : Set G), ((K'.relIndex K : ℕ) : ℂ)⁻¹ *
          ((((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
            ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K))) := by
        unfold twOrb
        refine finsum_congr fun c => ?_
        rw [avgK]; ring
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ c, ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
        rw [← mul_finsum]; congr 1; exact finsum_congr hc
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q, g q := by
        rw [← finsum_sigma_of_finite _ hsupp, finsum_comp_equiv e.symm]

end GlobalTheory.BCT.OrbLev
end
end
end
