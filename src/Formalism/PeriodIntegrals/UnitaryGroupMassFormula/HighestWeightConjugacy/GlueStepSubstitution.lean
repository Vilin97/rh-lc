module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.VmulCommEvPt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.LongestElementTranspose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.ChangeOfDens

section

@[expose] public section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def evM {ι : Type} (P : ι → ι → MvPolynomial (Vars L n) ℂ) (y : Vars L n → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MvPolynomial.eval y (P i j)

theorem mult_right (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (z : Vars L n → ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, evM P (vmul (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) z) =
      evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P z)
    (y : Vars L n → ℂ) (hy : InV y) : evM P (vmul y z) = evM P y * evM P z := by
  ext i j
  set g : Vars L n → MvPolynomial (Vars L n) ℂ :=
    fun p => ∑ k, MvPolynomial.C (z (p.1, k, p.2.2)) * MvPolynomial.X (p.1, p.2.1, k) with hg
  have hv : ∀ y' : Vars L n → ℂ, (fun p => MvPolynomial.eval y' (g p)) = vmul y' z := by
    intro y'
    funext p
    simp [hg, vmul, mul_comm]
  have hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (MvPolynomial.aeval g (P i j) -
      ∑ k, P i k * MvPolynomial.C (MvPolynomial.eval z (P k j))) =
      evM P (vmul y' z) i j - (evM P y' * evM P z) i j := by
    intro y'

    rw [map_sub, eval_aeval_eq, hv, map_sum]
    simp [evM, Matrix.mul_apply]
  have key := hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy
  rw [hF] at key
  exact sub_eq_zero.1 key

theorem mult_left (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (y : Vars L n → ℂ)
    (hrat : ∀ δ₀ ∈ GQ0 L n, evM P (vmul y (ratPt (δ₀ : Matrix (Fin n) (Fin n) L))) =
      evM P y * evM P (ratPt (δ₀ : Matrix (Fin n) (Fin n) L)))
    (z : Vars L n → ℂ) (hz : InV z) : evM P (vmul y z) = evM P y * evM P z := by
  ext i j
  set g : Vars L n → MvPolynomial (Vars L n) ℂ :=
    fun p => ∑ k, MvPolynomial.C (y (p.1, p.2.1, k)) * MvPolynomial.X (p.1, k, p.2.2) with hg
  have hv : ∀ z' : Vars L n → ℂ, (fun p => MvPolynomial.eval z' (g p)) = vmul y z' := by
    intro z'
    funext p
    simp [hg, vmul]
  have hF : ∀ z' : Vars L n → ℂ, MvPolynomial.eval z' (MvPolynomial.aeval g (P i j) -
      ∑ k, MvPolynomial.C (MvPolynomial.eval y (P i k)) * P k j) =
      evM P (vmul y z') i j - (evM P y * evM P z') i j := by
    intro z'

    rw [map_sub, eval_aeval_eq, hv, map_sum]
    simp [evM, Matrix.mul_apply]
  have key := hd L n _ (fun δ₀ hδ => by rw [hF, hrat δ₀ hδ, sub_self]) z hz
  rw [hF] at key
  exact sub_eq_zero.1 key

theorem mult_of_dens (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, ∀ δ₀ ∈ GQ0 L n,
      evM P (ratPt ((γ₀ * δ₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) =
        evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P (ratPt (δ₀ : Matrix (Fin n) (Fin n) L)))
    (y z : Vars L n → ℂ) (hy : InV y) (hz : InV z) : evM P (vmul y z) = evM P y * evM P z := by
  have hl : ∀ γ₀ ∈ GQ0 L n, ∀ z' : Vars L n → ℂ, InV z' →
      evM P (vmul (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) z') =
        evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P z' := by
    intro γ₀ hγ z' hz'
    apply mult_left hd P _ _ z' hz'
    intro δ₀ hδ
    rw [← hrat γ₀ hγ δ₀ hδ]
    congr 1
    funext p

    simp [vmul, ratPt, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]
  exact mult_right hd P z (fun γ₀ hγ => hl γ₀ hγ z hz) y hy

theorem change_of_dens (hd : DensStep) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (P : ι → ι → MvPolynomial (Vars L n) ℂ) (P' : ι' → ι' → MvPolynomial (Vars L n) ℂ)
    (C : Matrix ι ι' ℂ) (C' : Matrix ι' ι ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) =
      C * evM P' (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * C')
    (y : Vars L n → ℂ) (hy : InV y) : evM P y = C * evM P' y * C' := by
  ext i j
  have hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (P i j -
      ∑ l, ∑ k, MvPolynomial.C (C i k * C' l j) * P' k l) = evM P y' i j - (C * evM P' y' * C') i j := by
    intro y'

    rw [map_sub, map_sum]

    simp only [map_sum, map_mul, MvPolynomial.eval_C, evM, Matrix.of_apply, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key := hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy
  rw [hF] at key
  exact sub_eq_zero.1 key

theorem toGQ_mul (γ₀ δ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (hδ : δ₀ ∈ GQ0 L n) :
    toGQ (γ₀ * δ₀) (Subgroup.mul_mem _ hγ hδ) = toGQ γ₀ hγ * toGQ δ₀ hδ := by
  apply Subtype.ext
  apply Subtype.ext
  simp [toGQ, map_mul]

theorem toGQ_surj (γ : GQ L n) : ∃ γ₀ : GL (Fin n) L, ∃ hγ : γ₀ ∈ GQ0 L n, γ = toGQ γ₀ hγ := by
  obtain ⟨g, hg, h⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨g, hg, Subtype.ext (Subtype.ext h.symm)⟩

theorem span_orbit (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (x : a.W)
    (hx : x ≠ 0) :
    Submodule.span ℂ {w | ∃ γ : GQ L n, w = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)} = ⊤ := by
  classical
  set R : Set a.W := Set.range fun γ : GQ L n => a.ρ γ x with hR
  have hT : {w | ∃ γ : GQ L n, w = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)} =
      b.equivFun '' R := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image, hR, Set.mem_range, exists_exists_eq_and]
    have key : ∀ γ : GQ L n, b.equivFun (a.ρ γ x) = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x) := by
      intro γ
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, key γ⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, key γ⟩
  have hS : Submodule.span ℂ R = ⊤ := by
    haveI : IsSimpleModule (MonoidAlgebra ℂ (GQ L n)) a.ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule a.ρ).1 a.irr
    set m := a.ρ.asModuleEquiv.symm x with hm
    have hm0 : m ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hx
    have htop : Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m} = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ((Submodule.span_singleton_eq_bot).not.2 hm0)
    have halg : ∀ r : MonoidAlgebra ℂ (GQ L n), a.ρ.asAlgebraHom r x ∈ Submodule.span ℂ R := by
      intro r
      induction r using MonoidAlgebra.induction_linear with
      | zero => simp
      | add f g hf hg =>
        rw [map_add (f := _), LinearMap.add_apply]
        exact add_mem hf hg
      | single g c =>
        rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨g, rfl⟩)
    rw [eq_top_iff]
    intro w _
    have hw : a.ρ.asModuleEquiv.symm w ∈ Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m} := by
      rw [htop]; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hw
    have e : w = a.ρ.asAlgebraHom r x := by
      have h2 := congrArg a.ρ.asModuleEquiv hr
      rw [Representation.asModuleEquiv_map_smul, hm, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    rw [e]
    exact halg r
  rw [hT]
  have e2 : (b.equivFun : a.W → (ι → ℂ)) '' R = (b.equivFun.toLinearMap : a.W →ₗ[ℂ] (ι → ℂ)) '' R := rfl
  rw [e2, Submodule.span_image, hS, Submodule.map_top, LinearMap.range_eq_top]
  exact b.equivFun.surjective

end

end PI.UnitaryGroupMassFormula.HwConjInf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStepSubstitution

section

@[expose] public section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}


open Classical in
def subT (τ : L →+* ℂ) : Vars L n → MvPolynomial (Bool × Fin n × Fin n) ℂ := fun p =>
  if p.1 = τ then MvPolynomial.X (true, p.2.1, p.2.2)
  else if p.1 = ComplexEmbedding.conjugate τ then MvPolynomial.X (false, p.2.1, p.2.2)
  else MvPolynomial.C (if p.2.1 = p.2.2 then 1 else 0)

theorem eval_subT (τ : L →+* ℂ) (g : GL (Fin n) ℂ) :
    (fun p => MvPolynomial.eval (gPt g) (subT τ p)) = evPt τ g := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  unfold subT evPt
  split_ifs <;> simp_all [gPt]

end

theorem glue_holds_var : GlueStep := by
  intro hd hg L _ _ _ n a τ lam mu h1 h2
  obtain ⟨ι, hι, hdι, b, P, hP, v, hv0, hv⟩ := h1
  obtain ⟨ι', hι', hdι', b', P', hP', u, hu0, hu⟩ := h2
  have ratM : ∀ (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n),
      evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) = LinearMap.toMatrix b b (a.ρ (toGQ γ₀ hγ)) :=
    fun γ₀ hγ => by rw [hP _ γ₀ (toGQ_val γ₀ hγ)]; rfl
  have ratM' : ∀ (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n),
      evM P' (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) = LinearMap.toMatrix b' b' (a.ρ (toGQ γ₀ hγ)) :=
    fun γ₀ hγ => by rw [hP' _ γ₀ (toGQ_val γ₀ hγ)]; rfl
  have multP : ∀ y z, InV y → InV z → evM P (vmul y z) = evM P y * evM P z :=
    mult_of_dens hd P (fun γ₀ hγ δ₀ hδ => by
      rw [ratM _ (Subgroup.mul_mem _ hγ hδ), ratM γ₀ hγ, ratM δ₀ hδ, toGQ_mul, map_mul, LinearMap.toMatrix_mul])
  have changeP : ∀ y, InV y → evM P y = b.toMatrix b' * evM P' y * b'.toMatrix b :=
    change_of_dens hd P P' _ _ (fun γ₀ hγ => by
      rw [ratM γ₀ hγ, ratM' γ₀ hγ]
      exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' b b' _).symm)
  let R : GL (Fin n) ℂ → Matrix ι ι ℂ := fun g => evM P (evPt τ g)
  let Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ := fun i j => MvPolynomial.aeval (subT τ) (P i j)
  have hRQ : ∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j) := by
    intro g i j
    simp only [R, Q, evM, Matrix.of_apply, eval_aeval_eq, eval_subT]
  have hRmul : ∀ g h, R (g * h) = R g * R h := by
    intro g h
    simp only [R]
    rw [evPt_mul]
    exact multP _ _ (inV_evPt τ g) (inV_evPt τ h)
  let S : Set (Matrix ι ι ℂ) := {s | ∃ y, InV y ∧
    (∀ i j, y (τ, i, j) = (if i = j then 1 else 0) ∧ y (ComplexEmbedding.conjugate τ, i, j) = (if i = j then 1 else 0)) ∧
    s = evM P y}
  have hS : ∀ s ∈ S, ∀ g, s * R g = R g * s := by
    rintro s ⟨y, hy, hy1, rfl⟩ g
    simp only [R]
    rw [← multP _ _ hy (inV_evPt τ g), ← multP _ _ (inV_evPt τ g) hy, vmul_comm_evPt τ y hy1 g]
  have hspan : ∀ x : a.W, x ≠ 0 → Submodule.span ℂ
      {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) (b.equivFun x))} = ⊤ := by
    intro x hx
    rw [eq_top_iff, ← span_orbit a b x hx]
    apply Submodule.span_mono
    rintro w ⟨γ, rfl⟩
    obtain ⟨γ₀, hγ, rfl⟩ := toGQ_surj γ
    refine ⟨evM P (trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))),
      ⟨_, inV_trivAt τ _ (inV_ratPt γ₀ hγ), fun i j => ⟨trivAt_tau τ _ i j, trivAt_conj τ _ i j⟩, rfl⟩,
      Matrix.GeneralLinearGroup.map τ γ₀, ?_⟩
    rw [Matrix.mulVec_mulVec, ← ratM γ₀ hγ]
    simp only [R]
    rw [← multP _ _ (inV_trivAt τ _ (inV_ratPt γ₀ hγ)) (inV_evPt τ _), ← ratPt_split τ γ₀ hγ]
  let x' : a.W := b'.equivFun.symm u
  have hx' : x' ≠ 0 := by
    intro h
    apply hu0
    rw [← b'.equivFun.apply_symm_apply u]
    change b'.equivFun x' = 0
    rw [h, map_zero]
  have hxu : b.equivFun x' = Matrix.mulVec (b.toMatrix b') u := by
    have h3 := LinearMap.toMatrix_mulVec_repr b' b LinearMap.id x'
    rw [LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.id_apply] at h3
    rw [Module.Basis.equivFun_apply, ← h3]
    congr 1
    exact b'.equivFun.apply_symm_apply u
  have hv' : b.equivFun (b.equivFun.symm v) = v := b.equivFun.apply_symm_apply v
  have hvx : b.equivFun.symm v ≠ 0 := by
    intro h; apply hv0; rw [← hv', h, map_zero]
  have hũ0 : Matrix.mulVec (b.toMatrix b') u ≠ 0 := by
    rw [← hxu]; intro h; exact hx' (b.equivFun.injective (by rw [h, map_zero]))
  have huB : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id →
      Matrix.mulVec (R B) (Matrix.mulVec (b.toMatrix b') u) = (∏ i, B.val i i ^ mu i) • Matrix.mulVec (b.toMatrix b') u := by
    intro B hB
    have hc := changeP _ (inV_evPt τ B)
    simp only [R]
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_assoc, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
    have hu' := hu B hB
    change Matrix.mulVec (evM P' (evPt τ B)) u = _ at hu'
    rw [hu', Matrix.mulVec_smul]
  have spv := hspan _ hvx
  rw [hv'] at spv
  have spu := hspan _ hx'
  rw [hxu] at spu
  exact hg n ι R Q hRQ hRmul S hS v _ lam mu (fun B hB => hv B hB) huB spv spu hv0 hũ0

end PI.UnitaryGroupMassFormula.HwConjInf
end
end
end
