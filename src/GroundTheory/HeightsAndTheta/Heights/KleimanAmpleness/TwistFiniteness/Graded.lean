module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
public import Mathlib.Algebra.MonoidAlgebra.Grading
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.PsiOfIsHomogeneous

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra

noncomputable section

universe u w

namespace TwistFin

variable {Ω : Type w} [Field Ω] {N r : ℕ}

abbrev LA (Ω : Type w) [Field Ω] : Type w := AddMonoidAlgebra Ω (ℤ × ℤ)


set_option linter.unusedVariables false in
def Amb (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) : Type w := LA Ω

variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)

instance : AddCommGroup (Amb x η) := inferInstanceAs (AddCommGroup (LA Ω))

instance : Module (LA Ω) (Amb x η) := inferInstanceAs (Module (LA Ω) (LA Ω))

def toA : Amb x η ≃+ LA Ω := AddEquiv.refl _

variable (S : Type u) [CommRing S] [Algebra S Ω]

abbrev Sy (S : Type u) [CommRing S] (r : ℕ) : Type u := MvPolynomial (Fin (r + 1)) S

def psi : Sy S r →ₐ[S] LA Ω := aeval fun j => single ((0 : ℤ), (1 : ℤ)) (η j)

def phi : Poly (Sy S r) N →+* LA Ω :=
  eval₂Hom (psi η S).toRingHom fun i => single ((1 : ℤ), (0 : ℤ)) (x i)

instance modP : Module (Poly (Sy S r) N) (Amb x η) := Module.compHom _ (phi x η S)

instance modSy : Module (Sy S r) (Amb x η) := Module.compHom _ (psi η S).toRingHom

theorem toA_smulP (p : Poly (Sy S r) N) (a : Amb x η) : toA x η (p • a) = phi x η S p * toA x η a := rfl

theorem toA_smulSy (s : Sy S r) (a : Amb x η) : toA x η (s • a) = psi η S s * toA x η a := rfl

theorem phi_C (s : Sy S r) : phi x η S (C s) = psi η S s := eval₂Hom_C _ _ _

theorem phi_X (i : Fin (N + 1)) : phi x η S (X i) = single ((1 : ℤ), (0 : ℤ)) (x i) :=
  eval₂Hom_X' _ _ _

theorem psi_X (j : Fin (r + 1)) : psi η S (X j) = single ((0 : ℤ), (1 : ℤ)) (η j) :=
  aeval_X _ _

instance : IsScalarTower (Sy S r) (Poly (Sy S r) N) (Amb x η) where
  smul_assoc s p a := by
    apply (toA x η).injective
    rw [toA_smulP, toA_smulSy, toA_smulP, MvPolynomial.smul_eq_C_mul, map_mul, phi_C, mul_assoc]

abbrev tgr (c : ℤ) : Submodule Ω (LA Ω) := gradeBy Ω (AddMonoidHom.fst ℤ ℤ) c

theorem single_mem_tgr (c k : ℤ) (ω : Ω) : (single (c, k) ω : LA Ω) ∈ tgr c :=
  single_mem_gradeBy (R := Ω) (AddMonoidHom.fst ℤ ℤ) (c, k) ω

theorem algebraMap_LA (s : S) : algebraMap S (LA Ω) s = single ((0 : ℤ), (0 : ℤ)) (algebraMap S Ω s) :=
  rfl

theorem psi_mem_tgr (s : Sy S r) : psi η S s ∈ tgr 0 := by
  induction s using MvPolynomial.induction_on with
  | C a =>
    rw [psi, aeval_C, algebraMap_LA]
    exact single_mem_tgr 0 0 _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, psi_X]
    simpa using SetLike.mul_mem_graded hp (single_mem_tgr 0 1 (η j))

theorem phi_mem_tgr {p : Poly (Sy S r) N} {d : ℕ} (hp : p.IsHomogeneous d) :
    phi x η S p ∈ tgr (d : ℤ) := by
  classical

  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hdeg : ∑ i ∈ μ.support, μ i = d := by
    have := hp (mem_support_iff.mp hμ)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [phi, coe_eval₂Hom, eval₂_monomial]
  have h1 := psi_mem_tgr η S (AddMonoidAlgebra.coeff p μ)
  have h2 : (∏ i ∈ μ.support, (single ((1 : ℤ), (0 : ℤ)) (x i) : LA Ω) ^ μ i) ∈
      tgr (∑ i ∈ μ.support, ((μ i : ℕ) : ℤ)) := by
    refine SetLike.prod_mem_graded _ _ _ fun i _ => ?_
    simpa using SetLike.pow_mem_graded (μ i) (single_mem_tgr 1 0 (x i))
  have h3 := SetLike.mul_mem_graded h1 h2
  rw [zero_add, ← Nat.cast_sum, hdeg] at h3
  exact h3

def kapT : Polynomial Ω →ₐ[Ω] LA Ω := Polynomial.aeval (single ((1 : ℤ), (0 : ℤ)) 1)

def kapU : Polynomial Ω →ₐ[Ω] LA Ω := Polynomial.aeval (single ((0 : ℤ), (1 : ℤ)) 1)

theorem phi_map_C {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    phi x η S (MvPolynomial.map (C : S →+* Sy S r) f) = single ((e : ℤ), (0 : ℤ)) (aeval x f) := by
  have key : (phi x η S).comp (MvPolynomial.map (C : S →+* Sy S r)) =
      (kapT (Ω := Ω)).toRingHom.comp (cone (S := S) x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply, map_C, phi_C]
      change psi η S (C a) = kapT ((cone (S := S) x) (C a))
      rw [psi, aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, kapT,
        Polynomial.aeval_C, coe_algebraMap, Function.comp_apply, algebraMap_LA, Algebra.algebraMap_self,
        RingHom.id_apply]
      rfl
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, phi_X]
      change _ = kapT (coneGen x (X i))
      rw [coneGen, aeval_X, kapT, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, coe_algebraMap,
        Function.comp_apply, single_mul_single]
      simp
  have := congrArg (fun g => g f) key
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  change kapT (cone (S := S) x f) = _
  rw [cone_of_isHomogeneous x hf, kapT, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    coe_algebraMap, Function.comp_apply, single_pow, single_mul_single]
  simp [MvPolynomial.aeval_def]

theorem psi_of_isHomogeneous {h : Sy S r} {b : ℕ} (hh : h.IsHomogeneous b) :
    psi η S h = single ((0 : ℤ), (b : ℤ)) (aeval η h) := by
  have key : (psi η S).toRingHom = (kapU (Ω := Ω)).toRingHom.comp (coneGen (S := S) η).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change psi η S (C a) = kapU ((coneGen (S := S) η) (C a))
      rw [psi, aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, kapU,
        Polynomial.aeval_C, coe_algebraMap, Function.comp_apply, algebraMap_LA, Algebra.algebraMap_self,
        RingHom.id_apply]
      rfl
    · intro j
      change psi η S (X j) = kapU (coneGen η (X j))
      rw [psi_X, coneGen, aeval_X, kapU, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, coe_algebraMap,
        Function.comp_apply, single_mul_single]
      simp
  have := congrArg (fun g => g h) key
  change psi η S h = kapU (coneGen (S := S) η h) at this
  rw [this, coneGen_of_isHomogeneous η hh, kapU, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    coe_algebraMap, Function.comp_apply, single_pow, single_mul_single]
  simp [MvPolynomial.aeval_def]

end TwistFin

end

end GroundTheory.Heights₂.Heights.Kleiman
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.Graded

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra

noncomputable section

universe u w

namespace TwistFin

variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]

def projT (c : ℤ) : LA Ω →ₗ[Ω] LA Ω :=
  GradedAlgebra.proj (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) c

theorem projT_apply (c : ℤ) (a : LA Ω) :
    projT c a = (DirectSum.decompose (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) a c :
      LA Ω) :=
  GradedAlgebra.proj_apply _ _ _

theorem projT_mem (c : ℤ) (a : LA Ω) : projT c a ∈ tgr c := by
  rw [projT_apply]; exact Subtype.property _

theorem projT_of_mem {a : LA Ω} {d : ℤ} (ha : a ∈ tgr d) (c : ℤ) :
    projT c a = if d = c then a else 0 := by
  rw [projT_apply]
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ ha
  · exact DirectSum.decompose_of_mem_ne _ ha h

theorem projT_mul_of_mem {a : LA Ω} {d : ℤ} (ha : a ∈ tgr d) (b : LA Ω) (c : ℤ) :
    projT c (a * b) = a * projT (c - d) b := by
  have := DirectSum.coe_decompose_mul_add_of_left_mem
    (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) (j := c - d) ha (b := b)
  rw [add_sub_cancel] at this
  rw [projT_apply, projT_apply]
  exact this

theorem exists_sum_projT (a : LA Ω) : ∃ F : Finset ℤ, ∑ c ∈ F, projT c a = a := by
  classical
  refine ⟨(DirectSum.decompose (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) a).support, ?_⟩
  simp only [projT_apply]
  exact DirectSum.sum_support_decompose _ a

variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)

def genT (j : Fin n0) : Amb x η := (toA x η).symm (single (d0 j, 0) (g0 j))

def TMod : Submodule (Poly (Sy S r) N) (Amb x η) := Submodule.span _ (Set.range (genT x η n0 d0 g0))

instance TMod.finite : Module.Finite (Poly (Sy S r) N) (TMod x η S n0 d0 g0) :=
  Module.Finite.span_of_finite _ (Set.finite_range _)

theorem projT_mem_TMod {m : Amb x η} (hm : m ∈ TMod x η S n0 d0 g0) (c : ℤ) :
    (toA x η).symm (projT c (toA x η m)) ∈ TMod x η S n0 d0 g0 := by
  induction hm using Submodule.span_induction generalizing c with
  | mem m hm =>
    obtain ⟨j, rfl⟩ := hm
    rw [genT, AddEquiv.apply_symm_apply, projT_of_mem (single_mem_tgr _ _ _)]
    split_ifs
    · exact Submodule.subset_span ⟨j, rfl⟩
    · rw [map_zero]; exact zero_mem _
  | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact add_mem (ha c) (hb c)
  | smul p m _ hm =>
    have hsum : toA x η (p • m) = ∑ d ∈ Finset.range (p.totalDegree + 1),
        phi x η S (homogeneousComponent d p) * toA x η m := by

      rw [toA_smulP, ← Finset.sum_mul, ← map_sum, sum_homogeneousComponent]

    rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [projT_mul_of_mem (phi_mem_tgr x η S (homogeneousComponent_isHomogeneous d p))]
    have h := Submodule.smul_mem _ (homogeneousComponent d p) (hm (c - d))
    convert h using 1
    apply (toA x η).injective
    rw [toA_smulP, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

def pieceM (c : ℤ) : Submodule (Sy S r) (TMod x η S n0 d0 g0) where
  carrier := {m | toA x η (m : Amb x η) ∈ tgr c}
  add_mem' {a b} ha hb := by
    change toA x η ((a : Amb x η) + b) ∈ tgr c
    rw [map_add (toA x η)]
    exact add_mem ha hb
  zero_mem' := by
    change toA x η ((0 : TMod x η S n0 d0 g0) : Amb x η) ∈ tgr c
    rw [Submodule.coe_zero, map_zero]; exact zero_mem _
  smul_mem' s m hm := by
    change toA x η ((s • m : TMod x η S n0 d0 g0) : Amb x η) ∈ tgr c
    rw [Submodule.coe_smul_of_tower, toA_smulSy]
    simpa using SetLike.mul_mem_graded (psi_mem_tgr η S s) hm

theorem isInternal_pieceM : DirectSum.IsInternal (pieceM x η S n0 d0 g0) := by
  classical
  let 𝒜 := (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω))
  let pc : ∀ c, pieceM x η S n0 d0 g0 c →+ 𝒜 c := fun c =>
    { toFun := fun m => ⟨toA x η ((m : TMod x η S n0 d0 g0) : Amb x η), m.2⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let Φ : (DirectSum ℤ fun c => pieceM x η S n0 d0 g0 c) →+ DirectSum ℤ fun c => 𝒜 c :=
    DFinsupp.mapRange.addMonoidHom pc
  have hΦ : ∀ v, DirectSum.coeAddMonoidHom 𝒜 (Φ v) =
      toA x η ((DirectSum.coeAddMonoidHom (pieceM x η S n0 d0 g0) v : TMod x η S n0 d0 g0) : Amb x η) := by
    intro v
    induction v using DirectSum.induction_on with
    | zero => simp
    | of c m =>
      rw [DirectSum.coeAddMonoidHom_of]
      have : Φ (DirectSum.of (fun c => ↥(pieceM x η S n0 d0 g0 c)) c m) =
          DirectSum.of (fun c => ↥(𝒜 c)) c (pc c m) :=
        DFinsupp.mapRange_single (hf := fun c => map_zero (pc c))
      rw [this, DirectSum.coeAddMonoidHom_of]
      rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb, Submodule.coe_add]
  constructor
  · intro v w hvw
    have h1 : Φ v = Φ w := (gradeBy.isInternal (R := Ω) (AddMonoidHom.fst ℤ ℤ)).1 (by
      change DirectSum.coeAddMonoidHom 𝒜 (Φ v) = DirectSum.coeAddMonoidHom 𝒜 (Φ w)
      rw [hΦ, hΦ, hvw])
    refine DFinsupp.ext fun c => ?_
    have h2 := DFunLike.congr_fun h1 c
    have h3 : pc c (v c) = pc c (w c) := by
      rw [← DFinsupp.mapRange_apply (hf := fun c => map_zero (pc c)),
        ← DFinsupp.mapRange_apply (hf := fun c => map_zero (pc c))]
      exact h2
    have h4 : ((pc c (v c) : 𝒜 c) : LA Ω) = ((pc c (w c) : 𝒜 c) : LA Ω) := by rw [h3]
    exact Subtype.ext (Subtype.ext ((toA x η).injective h4))
  · intro m
    obtain ⟨F, hF⟩ := exists_sum_projT (toA x η (m : Amb x η))
    refine ⟨∑ c ∈ F, DirectSum.of (fun c => pieceM x η S n0 d0 g0 c) c
      ⟨⟨(toA x η).symm (projT c (toA x η (m : Amb x η))), projT_mem_TMod x η S n0 d0 g0 m.2 c⟩, by
        change toA x η ((toA x η).symm _) ∈ tgr c
        rw [AddEquiv.apply_symm_apply]; exact projT_mem c _⟩, ?_⟩
    apply Subtype.ext
    apply (toA x η).injective

    rw [map_sum]

    simp only [DirectSum.coeAddMonoidHom_of, Submodule.coe_sum, map_sum, AddEquiv.apply_symm_apply]
    exact hF

def tgraded : GradedPMod (Sy S r) N (TMod x η S n0 d0 g0) where
  piece := pieceM x η S n0 d0 g0
  isInternal := isInternal_pieceM x η S n0 d0 g0
  smul_mem d c p m hp hm := by
    change toA x η ((p • m : TMod x η S n0 d0 g0) : Amb x η) ∈ tgr (c + d)
    rw [Submodule.coe_smul, toA_smulP, add_comm]
    exact SetLike.mul_mem_graded (phi_mem_tgr x η S hp) hm

end TwistFin

end

end GroundTheory.Heights₂.Heights.Kleiman
end
end
