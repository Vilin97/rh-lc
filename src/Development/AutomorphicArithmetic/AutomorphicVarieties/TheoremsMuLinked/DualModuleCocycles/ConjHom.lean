module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Kill0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrSingle

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.IdemDiag

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.idemDiag :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (e : Fin n → Matrix (Fin n) (Fin n) O), CompleteOrthogonalIdempotents e → (∀ i, (e i).trace = 1) → ∃ Q : GL (Fin n) O, ∀ i, ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * e i * (Q : Matrix (Fin n) (Fin n) O) = Matrix.single i i 1 := by
  intro O _ _ n e he htr
  classical
  have hmul : ∀ i j, e i * e j = if i = j then e i else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      exact (he.idem i).eq
    · exact he.ortho hij
  have hentry : ∀ i j a b, (e i * e j) a b = if i = j then e i a b else 0 := by
    intro i j a b
    rw [hmul]
    split_ifs <;> simp
  have hc : ∀ i, ∃ c, IsUnit (e i c c) := by
    intro i
    by_contra hne
    push_neg at hne
    have hmem : (e i).trace ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ (fun c _ => (IsLocalRing.mem_maximalIdeal _).mpr (hne c))
    rw [htr i] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem isUnit_one
  choose c hcu using hc
  let Qm : Matrix (Fin n) (Fin n) O := Matrix.of fun r j => e j r (c j)
  let Sm : Matrix (Fin n) (Fin n) O := Matrix.of fun i r => e i (c i) r
  have hSQ : Sm * Qm = Matrix.diagonal fun i => e i (c i) (c i) := by
    ext i j
    change (e i * e j) (c i) (c j) = _
    rw [hentry, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rfl
    · rfl
  have hdet : IsUnit (Sm * Qm).det := by
    rw [hSQ, Matrix.det_diagonal]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hcu i)
  rw [Matrix.det_mul] at hdet
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det Qm).mpr (isUnit_of_mul_isUnit_right hdet)
  refine ⟨U, fun i => ?_⟩
  have heQ : e i * Qm = Qm * Matrix.single i i 1 := by
    ext r j
    change (e i * e j) r (c j) = _
    rw [hentry, Matrix.mul_apply]
    simp only [Matrix.single_apply, Qm, Matrix.of_apply]
    split_ifs with h
    · subst h
      simp
    · simp [h]
  rw [mul_assoc, hU, heQ, ← hU, Units.inv_mul_cancel_left]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftOfS

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftOfS :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R) (b : O), IsDer x δ → (∀ (r : R) a, ρ (r • a) = x r • ρ a) → (∀ a, (ρ a).trace = x (τ a)) → x β = b → (∀ a a', s a * s a' = β • s (a * a')) → (∀ a, (s a).map x = b • ρ a) → (∀ a, (s a).trace = β * τ a) → ∃ d : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ (b * b) d := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ τ s β b hδ hρ htr hβ hs hx hst
  have hx' : ∀ a i j, x (s a i j) = b * ρ a i j := fun a i j => congrFun (congrFun (hx a) i) j
  have sm : ∀ (a : O) (y : X), a • y = algebraMap O X a * y := fun a y => Algebra.smul_def a y
  have en : ∀ a i j, (b • ((s a).map δ - δ β • bar X (ρ a))) i j =
      algebraMap O X b * (δ (s a i j) - δ β * algebraMap O X (ρ a i j)) := fun a i j => by
    rw [Matrix.smul_apply, sm]; rfl
  refine ⟨{ toFun := fun a => b • ((s a).map δ - δ β • bar X (ρ a))
            map_zero' := by ext i j; simp [bar]
            map_add' := fun a a' => by
              ext i j
              rw [Matrix.add_apply, en, en, en, map_add s, map_add ρ, Matrix.add_apply, Matrix.add_apply, map_add (f := _), map_add (f := _)]
              ring }, fun a a' => ?_, fun r a => ?_, fun a => ?_⟩
  · ext i k
    have h1 := congrArg δ (congrFun (congrFun (hs a a') i) k)

    rw [Matrix.mul_apply, map_sum, Matrix.smul_apply, smul_eq_mul, hδ β, hβ, hx'] at h1
    simp only [hδ _ _, hx', sm, map_mul] at h1
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, Matrix.mul_apply, en, Matrix.map_apply]
    rw [mul_sub, eq_sub_of_add_eq h1.symm]

    simp only [Matrix.mul_apply, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · ext i j
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, en]
    rw [Matrix.smul_apply, en, Matrix.smul_apply, map_smul s, hρ, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hδ r, hx']
    simp only [sm, map_mul, Matrix.map_apply]
    ring
  · have h1 : ((s a).map δ).trace = δ (s a).trace := by simp [Matrix.trace, map_sum]
    have h2 : (bar X (ρ a)).trace = algebraMap O X (ρ a).trace := by simp [bar, Matrix.trace, map_sum]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.trace_smul, Matrix.trace_sub, h1, h2, hst, hδ _ _, hβ, htr]
    simp only [sm, map_mul, smul_eq_mul]
    ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ConjHom

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private def conjHom {O : Type} [CommRing O] {n : ℕ} (Q : GL (Fin n) O) :
    Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) O where
  toFun Z := ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z * (Q : Matrix (Fin n) (Fin n) O)
  map_one' := by rw [Matrix.mul_one, Units.inv_mul]
  map_mul' a b := by
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]

theorem UpperTheory.V.Th.Coc.liftG :
    ∀ {n : ℕ} {O R X G : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing X] [Algebra O X] [Group G] (D : GDet n R G) (χ : Fin n → G →* (ResidueField O)ˣ) (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), 1 ≤ n → Function.Injective χ → D.map (res O R : R →+* ResidueField O) = GDet.ofRep (diagRep χ) → D.map x.toRingHom = GDet.ofRep ρ → c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsDer x δ → ∃ d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x ρ) D.tr (c₀ ^ (2 * n) * c₀ ^ (2 * n)) d := by
  intro n O R X G _ _ _ _ _ _ _ _ _ D χ x δ ρ c₀ hn hχ hres hx hc hspan hδ
  obtain ⟨E, _, _, π, τ, e, hπ, hτ, hg⟩ := UpperTheory.V.Th.Coc.gma (O := O) D χ hn hχ hres
  obtain ⟨htr, hsm, -⟩ := UpperTheory.V.Th.Coc.trRep D x ρ hn hx
  obtain ⟨k1, -⟩ := UpperTheory.V.Th.Coc.kill0 ρ c₀ hc hspan
  have hs : ∀ g, repR x ρ (MonoidAlgebra.single g (1 : R)) = ρ g := fun g => by
    rw [repR_single, map_one, one_smul]
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker (repR x ρ) := by
    intro y hy
    have hy' : π y = 0 := hy
    refine k1 _ fun g => ?_
    have h := htr (MonoidAlgebra.single g 1 * y)
    rw [map_mul, hs, ← hτ, map_mul, hy', mul_zero, map_zero, map_zero] at h
    exact h
  obtain ⟨ρE, hρE⟩ : ∃ ρE : E →+* Matrix (Fin n) (Fin n) O, ∀ y, ρE (π y) = repR x ρ y :=
    ⟨π.toRingHom.liftOfSurjective hπ ⟨repR x ρ, hker⟩, fun y =>
      π.toRingHom.liftOfRightInverse_comp_apply _ _ ⟨repR x ρ, hker⟩ y⟩
  have htrE : ∀ a, (ρE a).trace = x (τ a) := fun a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [hρE, htr, hτ]
  have hsmE : ∀ (r : R) a, ρE (r • a) = x r • ρE a := fun r a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [← map_smul π, hρE, hρE, hsm]
  have hrange : ∀ Z ∈ Submodule.span O (Set.range ρ), ∃ a, ρE a = Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, rfl⟩ := hZ
      exact ⟨π (MonoidAlgebra.single g 1), by rw [hρE, hs]⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | smul o a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨algebraMap O R o • a', by rw [hsmE, AlgHom.commutes]; rfl⟩
  obtain ⟨Q, hQ⟩ := UpperTheory.V.Th.Coc.idemDiag (fun i => ρE (e i)) (hg.idem.map ρE)
    (fun i => by rw [htrE, hg.one, map_one])
  let ρ' : E →+* Matrix (Fin n) (Fin n) O := (conjHom Q).comp ρE
  have hρ' : ∀ a, ρ' a = ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ρE a * (Q : Matrix (Fin n) (Fin n) O) :=
    fun a => rfl
  have htr' : ∀ a, (ρ' a).trace = x (τ a) := fun a => by
    rw [hρ', Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, htrE]
  have hsm' : ∀ (r : R) a, ρ' (r • a) = x r • ρ' a := fun r a => by
    rw [hρ', hρ', hsmE, Matrix.mul_smul, Matrix.smul_mul]
  have hsurj' : ∀ Z, ∃ a, ρ' a = c₀ • Z := fun Z => by
    obtain ⟨a, ha⟩ := hrange _ (hspan ((Q : Matrix (Fin n) (Fin n) O) * Z *
      ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))
    refine ⟨a, ?_⟩
    rw [hρ', ha, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]
  obtain ⟨s, β, hβ, h1, h2, h3⟩ := UpperTheory.V.Th.Coc.smat x ρ' τ e c₀ hn hg hQ htr' hsurj'
  obtain ⟨d, hd⟩ := UpperTheory.V.Th.Coc.liftOfS x δ ρ' τ s β (c₀ ^ (2 * n)) hδ hsm' htr' hβ h1 h2 h3
  obtain ⟨d', hd', -⟩ := UpperTheory.V.Th.Coc.liftConj x δ ρE ρ' τ _ Q d (fun a => by
    rw [hρ']
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]) hd
  refine ⟨d'.comp π.toRingHom.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b
    have h := hd'.mul (π a) (π b)
    rw [← map_mul, hρE, hρE] at h
    exact h
  · intro r a
    have h := hd'.smul r (π a)
    rw [← map_smul π, hρE] at h
    exact h
  · intro a
    have h := hd'.tr (π a)
    rw [hτ] at h
    exact h
end
end
